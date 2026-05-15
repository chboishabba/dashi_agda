#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import re
from pathlib import Path
from typing import Any

import numpy as np


DEFAULT_STRICT_ARTIFACT = Path("scripts/data/outputs/t43_strict_log_sigma_dashi_v4_20260515.json")
DEFAULT_OUTPUT = Path("scripts/data/outputs/dyturbo_t43_direct_strict_log_20260516.json")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _is_float_token(token: str) -> bool:
    try:
        float(token)
    except ValueError:
        return False
    return True


def _extract_h1_values(dat_path: Path, hist_name: str) -> list[float]:
    text = dat_path.read_text(encoding="utf-8", errors="ignore")
    wanted_spaced = " ".join(hist_name)
    candidates = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line.startswith("h 1 "):
            continue
        compact_tail = "".join(line.split()[-40:])
        if hist_name not in compact_tail and wanted_spaced not in line:
            continue
        tokens = line.split()
        try:
            n_edges = int(tokens[2])
            after_edges = 3 + n_edges
            n_cells = int(tokens[after_edges + 2])
        except (IndexError, ValueError) as exc:
            raise ValueError(f"cannot parse H1 header for {hist_name} in {dat_path}") from exc

        data_start = after_edges + 5
        data_tokens = []
        for token in tokens[data_start:]:
            if not _is_float_token(token):
                break
            data_tokens.append(token)
        # The serialized histogram appends a numeric histogram-name length before
        # the spaced name.  Keep only visible-bin plus overflow pairs.
        expected_with_overflow = 2 * n_edges
        expected_visible_only = 2 * (n_edges - 1)
        if len(data_tokens) >= expected_with_overflow:
            data_tokens = data_tokens[:expected_with_overflow]
        elif len(data_tokens) >= expected_visible_only:
            data_tokens = data_tokens[:expected_visible_only]
        if len(data_tokens) % 2 != 0 or len(data_tokens) < expected_visible_only:
            raise ValueError(f"cannot parse H1 data for {hist_name} in {dat_path}")
        pairs = [
            (float(data_tokens[index]), float(data_tokens[index + 1]))
            for index in range(0, len(data_tokens), 2)
        ]
        if len(pairs) < n_edges - 1:
            raise ValueError(f"H1 {hist_name} has too few cells in {dat_path}")
        # DYTurbo STL histograms store the visible bins followed by overflow.
        candidates.append([value for value, _err in pairs[: n_edges - 1]])
    if not candidates:
        raise ValueError(f"histogram {hist_name} not found in {dat_path}")
    return candidates[-1]


def _failure(reason: str, args: argparse.Namespace, **extra: Any) -> dict[str, Any]:
    payload = {
        "artifact_schema": "dashi.dyturbo.t43_direct_strict_log.v1",
        "status": "blocked",
        "failure_reason": reason,
        "numerator_dat": args.numerator_dat,
        "denominator_dat": args.denominator_dat,
        "strict_artifact": args.strict_artifact,
        "promotes": False,
    }
    payload.update(extra)
    return payload


def compute(args: argparse.Namespace) -> dict[str, Any]:
    strict = _load_json(Path(args.strict_artifact))
    n_bins = len(strict["per_bin"])
    try:
        numerator = np.asarray(_extract_h1_values(Path(args.numerator_dat), "xs_qt"), dtype=float)
        denominator = np.asarray(_extract_h1_values(Path(args.denominator_dat), "xs_qt"), dtype=float)
    except ValueError as exc:
        return _failure(str(exc), args)
    if len(numerator) != n_bins or len(denominator) != n_bins:
        return _failure(
            f"DYTurbo histogram bins do not match strict artifact: num={len(numerator)} den={len(denominator)} strict={n_bins}",
            args,
        )
    if not np.all(np.isfinite(numerator)) or not np.all(np.isfinite(denominator)):
        return _failure("DYTurbo xs_qt contains non-finite values", args)
    if not np.all(numerator > 0.0) or not np.all(denominator > 0.0):
        non_positive_numerator = np.where(numerator <= 0.0)[0]
        non_positive_denominator = np.where(denominator <= 0.0)[0]
        return _failure(
            "DYTurbo xs_qt has non-positive bins; increase statistics or change provider settings",
            args,
            n_bins=n_bins,
            non_positive_numerator_bins=[int(index) for index in non_positive_numerator],
            non_positive_denominator_bins=[int(index) for index in non_positive_denominator],
            numerator_xs_qt=[float(value) for value in numerator],
            denominator_xs_qt=[float(value) for value in denominator],
        )

    ratio = numerator / denominator
    if not np.all(ratio > 0.0):
        return _failure("DYTurbo t43 ratio has non-positive bins", args)

    log_prediction = np.log(ratio)
    log_data = np.asarray(strict["strictComparison"]["logData"], dtype=float)
    covariance = np.asarray(strict["strictComparison"]["propagatedCovariance"], dtype=float)
    cov_inv = np.linalg.inv(covariance)
    residual = log_prediction - log_data
    chi2 = float(residual @ cov_inv @ residual)
    chi2_per_dof = chi2 / n_bins
    strict_pass = bool(chi2_per_dof <= args.threshold)
    return {
        "artifact_schema": "dashi.dyturbo.t43_direct_strict_log.v1",
        "status": "computed",
        "provider": "DYTurbo-1.4.2-direct-fiducial-xs_qt",
        "provider_role": "direct fiducial t43 ratio prediction, not a pure hadronic W_i grid",
        "numerator_dat": args.numerator_dat,
        "denominator_dat": args.denominator_dat,
        "strict_artifact": args.strict_artifact,
        "n_bins": n_bins,
        "threshold": args.threshold,
        "chi2": chi2,
        "chi2_per_dof": chi2_per_dof,
        "strict_pass": strict_pass,
        "promotes": strict_pass,
        "numerator_xs_qt": [float(value) for value in numerator],
        "denominator_xs_qt": [float(value) for value in denominator],
        "prediction_ratio": [float(value) for value in ratio],
        "log_prediction": [float(value) for value in log_prediction],
        "log_residuals": [float(value) for value in residual],
        "promotion_boundary": (
            "direct DYTurbo fiducial route promotes only if strict-log chi2/dof <= threshold; "
            "it does not satisfy the independent W_i provider contract"
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compute strict-log t43 chi2 from direct DYTurbo numerator/denominator xs_qt histograms."
    )
    parser.add_argument("--numerator-dat", required=True)
    parser.add_argument("--denominator-dat", required=True)
    parser.add_argument("--strict-artifact", default=str(DEFAULT_STRICT_ARTIFACT))
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--threshold", type=float, default=2.0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = compute(args)
    _write_json(Path(args.output), payload)
    print(f"DYTurbo direct strict-log artifact written: {args.output}")
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
