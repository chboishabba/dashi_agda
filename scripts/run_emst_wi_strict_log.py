#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


DEFAULT_STRICT_ARTIFACT = Path("scripts/data/outputs/t43_strict_log_sigma_dashi_v4_20260515.json")
DEFAULT_COEFFICIENTS = Path("scripts/data/outputs/emst_nine_component_C_fid_sigma_dashi_v4_20260515.json")
DEFAULT_WI_PROVIDER = Path("scripts/data/outputs/emst_wi_provider_contract_20260516.json")
DEFAULT_OUTPUT = Path("scripts/data/outputs/emst_wi_strict_log_result_20260516.json")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _as_matrix(values: Any, name: str, rows: int, columns: int) -> np.ndarray:
    matrix = np.asarray(values, dtype=float)
    if matrix.shape != (rows, columns):
        raise ValueError(f"{name} has shape {matrix.shape}, expected {(rows, columns)}")
    if not np.all(np.isfinite(matrix)):
        raise ValueError(f"{name} contains non-finite values")
    return matrix


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _failure_payload(reason: str, args: argparse.Namespace) -> dict[str, Any]:
    return {
        "artifact_schema": "dashi.emst.wi_strict_log_result.v1",
        "status": "blocked",
        "failure_reason": reason,
        "wi_provider_artifact": args.wi_provider,
        "strict_artifact": args.strict_artifact,
        "coefficient_artifact": args.coefficients,
        "promotes": False,
        "promotion_boundary": (
            "strict-log result requires a valid independent W_i provider artifact "
            "and positive pre-normalized fiducial prediction"
        ),
    }


def compute(args: argparse.Namespace) -> dict[str, Any]:
    provider = _load_json(Path(args.wi_provider))
    if provider.get("status") != "valid_independent_wi_grid":
        return _failure_payload(
            f"W_i provider status is {provider.get('status')!r}, expected 'valid_independent_wi_grid'",
            args,
        )
    if not provider.get("provider_metadata", {}).get("not_derived_from_sigma_inclusive", False):
        return _failure_payload("W_i provider independence assertion is absent", args)

    strict = _load_json(Path(args.strict_artifact))
    coeff = _load_json(Path(args.coefficients))
    rows = provider.get("rows", [])
    if not isinstance(rows, list) or not rows:
        return _failure_payload("W_i provider contains no validated rows", args)

    n_bins = len(strict["per_bin"])
    n_components = 9
    if len(rows) != n_bins:
        return _failure_payload(f"W_i provider row count {len(rows)} does not match strict bins {n_bins}", args)

    wi = np.zeros((n_components, n_bins), dtype=float)
    phi_provider = np.zeros(n_bins, dtype=float)
    for column, row in enumerate(rows):
        phi_provider[column] = float(row["phi_star"])
        for component in range(n_components):
            wi[component, column] = float(row[f"W{component}"])

    phi_strict = np.asarray([float(item["phiStar"]) for item in strict["per_bin"]], dtype=float)
    phi_delta = np.max(np.abs(phi_provider - phi_strict))
    if phi_delta > args.phi_tolerance:
        return _failure_payload(f"W_i provider phi grid delta {phi_delta} exceeds {args.phi_tolerance}", args)

    coefficient_key = (
        "C_fid_acceptance_mean" if args.coefficient_mode == "acceptance-mean"
        else "C_fid_integral_over_4pi"
    )
    c_fid = _as_matrix(coeff[coefficient_key], coefficient_key, n_components, n_bins)
    sigma_fid = np.sum(wi * c_fid, axis=0)
    positive_pre_normalization = bool(np.all(sigma_fid > 0.0))
    if not positive_pre_normalization:
        return _failure_payload("fiducial prediction has non-positive bins before any normalization", args)

    normalization_mode = "none"
    normalization_factor = 1.0
    if args.allow_log_mean_normalization:
        log_data = np.asarray(strict["strictComparison"]["logData"], dtype=float)
        normalization_factor = float(np.exp(np.mean(log_data) - np.mean(np.log(sigma_fid))))
        sigma_fid = sigma_fid * normalization_factor
        normalization_mode = "diagnostic_log_mean_normalization"

    log_prediction = np.log(sigma_fid)
    log_data = np.asarray(strict["strictComparison"]["logData"], dtype=float)
    residual = log_prediction - log_data
    covariance = np.asarray(strict["strictComparison"]["propagatedCovariance"], dtype=float)
    cov_inv = np.linalg.inv(covariance)
    chi2 = float(residual @ cov_inv @ residual)
    chi2_per_dof = chi2 / n_bins
    strict_pass = bool(chi2_per_dof <= args.threshold)
    promotable = bool(strict_pass and normalization_mode == "none")

    return {
        "artifact_schema": "dashi.emst.wi_strict_log_result.v1",
        "status": "computed",
        "wi_provider_artifact": args.wi_provider,
        "strict_artifact": args.strict_artifact,
        "coefficient_artifact": args.coefficients,
        "coefficient_mode": args.coefficient_mode,
        "normalization_mode": normalization_mode,
        "normalization_factor": normalization_factor,
        "provider_metadata": provider.get("provider_metadata", {}),
        "n_bins": n_bins,
        "n_components": n_components,
        "max_phi_abs_delta": float(phi_delta),
        "positive_pre_normalization": positive_pre_normalization,
        "chi2": chi2,
        "chi2_per_dof": chi2_per_dof,
        "threshold": args.threshold,
        "strict_pass": strict_pass,
        "promotes": promotable,
        "log_prediction": [float(value) for value in log_prediction],
        "log_residuals": [float(value) for value in residual],
        "sigma_fiducial_prediction": [float(value) for value in sigma_fid],
        "promotion_boundary": (
            "promotes only if chi2/dof <= threshold with normalization_mode=none; "
            "diagnostic normalization is explicitly non-promoting"
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Consume a validated independent EMST W_i grid and compute strict-log chi2."
    )
    parser.add_argument("--wi-provider", default=str(DEFAULT_WI_PROVIDER))
    parser.add_argument("--strict-artifact", default=str(DEFAULT_STRICT_ARTIFACT))
    parser.add_argument("--coefficients", default=str(DEFAULT_COEFFICIENTS))
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument(
        "--coefficient-mode",
        choices=["integral-over-4pi", "acceptance-mean"],
        default="integral-over-4pi",
    )
    parser.add_argument("--threshold", type=float, default=2.0)
    parser.add_argument("--phi-tolerance", type=float, default=1e-12)
    parser.add_argument(
        "--allow-log-mean-normalization",
        action="store_true",
        help="Diagnostic only. Applies posterior log-mean normalization and cannot promote.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = compute(args)
    _write_json(Path(args.output), payload)
    print(f"EMST W_i strict-log result written: {args.output}")
    print(f"status: {payload['status']}")
    if payload["status"] != "computed":
        print(f"blocked: {payload['failure_reason']}")
        return 2
    print(f"chi2/dof: {payload['chi2_per_dof']:.6f}")
    print(f"strict_pass: {payload['strict_pass']}")
    print(f"promotes: {payload['promotes']}")
    return 0 if payload["promotes"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
