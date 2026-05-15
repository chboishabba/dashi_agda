#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from run_t43_projection import T44_PATH, parse_t44


DEFAULT_INPUT = Path("scripts/data/outputs/t43_strict_log_sigma_dashi_v4_20260515.json")
DEFAULT_OUTPUT = Path("scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json")


def _trbd_projection(
    residual: np.ndarray,
    basis: np.ndarray,
    cov_inv: np.ndarray,
    chi2_raw: float,
) -> dict[str, Any]:
    normal = basis.T @ cov_inv @ basis
    rhs = basis.T @ cov_inv @ residual
    coeff = np.linalg.solve(normal, rhs)
    residual_perp = residual - basis @ coeff
    chi2_perp = float(residual_perp @ cov_inv @ residual_perp)
    dof_perp = len(residual) - basis.shape[1]
    return {
        "basis_dim": int(basis.shape[1]),
        "coefficients": [float(value) for value in coeff],
        "chi2_perp": chi2_perp,
        "chi2_perp_per_dof": chi2_perp / dof_perp,
        "coverage": 1.0 - chi2_perp / chi2_raw,
        "dof_perp": int(dof_perp),
        "residual_perp": residual_perp,
    }


def _promotability_label(chi2_per_dof: float) -> str:
    if chi2_per_dof <= 2.0:
        return "pass"
    if chi2_per_dof <= 20.0:
        return "partial"
    return "blocked"


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise TypeError(f"{path}: expected JSON object")
    return payload


def _per_bin_arrays(payload: dict[str, Any]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    rows = payload.get("per_bin")
    if not isinstance(rows, list) or not rows:
        raise ValueError("strict-log artifact is missing non-empty per_bin records")

    phi_star = np.array([float(row["phiStar"]) for row in rows], dtype=float)
    data = np.array([float(row["data"]) for row in rows], dtype=float)
    pred = np.array([float(row["pred"]) for row in rows], dtype=float)
    if np.any(phi_star <= 0.0) or np.any(data <= 0.0) or np.any(pred <= 0.0):
        raise ValueError("strict-log slope decomposition requires positive phiStar, data, and prediction values")
    return phi_star, data, pred


def _load_log_covariance(payload: dict[str, Any], data: np.ndarray) -> np.ndarray:
    strict = payload.get("strictComparison")
    propagated = strict.get("propagatedCovariance") if isinstance(strict, dict) else None
    if propagated is not None:
        return np.array(propagated, dtype=float)

    bins = payload.get("bins")
    if not isinstance(bins, list) or not bins:
        raise ValueError("artifact has neither strictComparison.propagatedCovariance nor bins for t44 parsing")
    t44 = parse_t44(T44_PATH, bins)
    raw_cov = np.array(t44["covariance"], dtype=float)
    return raw_cov / np.outer(data, data)


def decompose(input_path: Path, output_path: Path) -> dict[str, Any]:
    payload = _load_json(input_path)
    phi_star, data, pred = _per_bin_arrays(payload)
    log_cov = _load_log_covariance(payload, data)
    cov_inv = np.linalg.inv(log_cov)
    cov_inv = 0.5 * (cov_inv + cov_inv.T)

    log_phi = np.log(phi_star)
    basis = np.column_stack([np.ones_like(log_phi), log_phi])
    basis_quad = np.column_stack([np.ones_like(log_phi), log_phi, log_phi**2])
    basis_cubic = np.column_stack([np.ones_like(log_phi), log_phi, log_phi**2, log_phi**3])
    log_data = np.log(data)
    log_pred = np.log(pred)
    residual_pred_minus_data = log_pred - log_data

    n_bins = len(phi_star)
    chi2_raw = float(residual_pred_minus_data @ cov_inv @ residual_pred_minus_data)
    chi2_per_dof_raw = chi2_raw / n_bins
    linear_projection = _trbd_projection(residual_pred_minus_data, basis, cov_inv, chi2_raw)
    quad_projection = _trbd_projection(residual_pred_minus_data, basis_quad, cov_inv, chi2_raw)
    cubic_projection = _trbd_projection(residual_pred_minus_data, basis_cubic, cov_inv, chi2_raw)

    normal = basis.T @ cov_inv @ basis
    residual_coeff = np.array(linear_projection["coefficients"], dtype=float)
    shape_component = basis @ residual_coeff
    residual_corrected = linear_projection["residual_perp"]
    chi2_corrected = float(linear_projection["chi2_perp"])
    chi2_per_dof_corrected = chi2_corrected / (n_bins - 2)
    chi2_shape = float(shape_component @ cov_inv @ shape_component)
    chi2_cross = float(2.0 * shape_component @ cov_inv @ residual_corrected)
    fraction_shape = float(linear_projection["coverage"])

    diag_inv = np.diag(cov_inv)
    per_bin_chi2_after_linear = residual_corrected**2 * diag_inv
    top_residual_bins = [int(value) for value in np.argsort(per_bin_chi2_after_linear)[-5:][::-1]]
    peak_bin = top_residual_bins[0]

    data_coeff = np.linalg.solve(normal, basis.T @ cov_inv @ log_data)
    pred_coeff = np.linalg.solve(normal, basis.T @ cov_inv @ log_pred)
    slope_data_observed = float(data_coeff[1])
    slope_dashi_v4 = float(pred_coeff[1])
    residual_slope_pred_minus_data = float(residual_coeff[1])
    slope_correction_needed_for_prediction = slope_data_observed - slope_dashi_v4

    existing_diag = (
        payload.get("strictComparison", {})
        .get("diagnostics", {})
        .get("logPhiLinearSubspaceDiagnostic", {})
    )
    artifact = {
        "source_artifact": str(input_path),
        "basis": "span_1_log_phiStar",
        "protocol": "strict_log_covariance_weighted_wls_projection",
        "residual_convention": "log(prediction) - log(data)",
        "covariance_law": "C_log[i,j] = C_raw[i,j] / (R_data[i] * R_data[j])",
        "n_bins": n_bins,
        "chi2_raw": chi2_raw,
        "chi2_per_dof_raw": chi2_per_dof_raw,
        "chi2_corrected_after_shape_removal": chi2_corrected,
        "chi2_per_dof_corrected_after_shape_removal": chi2_per_dof_corrected,
        "chi2_shape": chi2_shape,
        "chi2_cross": chi2_cross,
        "chi2_fraction_from_shape": fraction_shape,
        "intercept_fit_pred_minus_data": float(residual_coeff[0]),
        "slope_fit_pred_minus_data": residual_slope_pred_minus_data,
        "slope_dashi_v4": slope_dashi_v4,
        "slope_data_observed": slope_data_observed,
        "slope_correction_needed_for_prediction": slope_correction_needed_for_prediction,
        "strict_pass_after_shape_removal": chi2_per_dof_corrected <= 2.0,
        "existing_runner_log_phi_diagnostic": existing_diag,
        "extended_basis_decomposition": {
            "basis_source": "Structural_QCD_log_series",
            "log_linear": {
                key: value
                for key, value in linear_projection.items()
                if key != "residual_perp"
            },
            "log_quadratic": {
                key: value
                for key, value in quad_projection.items()
                if key != "residual_perp"
            },
            "log_cubic": {
                key: value
                for key, value in cubic_projection.items()
                if key != "residual_perp"
            },
            "peak_residual_bin_after_linear": int(peak_bin),
            "peak_residual_phi_star_after_linear": float(phi_star[peak_bin]),
            "peak_residual_per_bin_chi2_after_linear_diag_approx": float(
                per_bin_chi2_after_linear[peak_bin]
            ),
            "top_residual_bins_after_linear": top_residual_bins,
            "top_residual_phi_star_after_linear": [
                float(phi_star[index]) for index in top_residual_bins
            ],
            "log_quadratic_promotability": _promotability_label(
                quad_projection["chi2_perp_per_dof"]
            ),
            "log_cubic_promotability": _promotability_label(
                cubic_projection["chi2_perp_per_dof"]
            ),
        },
        "promotability_assessment": (
            "shape component dominates, but corrected chi2/dof remains above 2; residual obstruction remains"
            if chi2_per_dof_corrected > 2.0
            else "shape correction is numerically sufficient; derivation still required before promotion"
        ),
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", encoding="utf-8") as handle:
        json.dump(artifact, handle, indent=2, sort_keys=True)
        handle.write("\n")
    return artifact


def main() -> int:
    parser = argparse.ArgumentParser(description="Decompose t43 strict-log residual over span(1, log(phiStar)).")
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    artifact = decompose(args.input, args.output)
    print("=" * 60)
    print("span(1, log(phiStar)) STRICT-LOG SLOPE DECOMPOSITION")
    print("=" * 60)
    print(f"  Bins (below-Z):                 {artifact['n_bins']}")
    print(f"  chi2/dof raw:                   {artifact['chi2_per_dof_raw']:.6f}")
    print(f"  chi2/dof after shape removal:   {artifact['chi2_per_dof_corrected_after_shape_removal']:.6f}")
    print(f"  chi2 fraction from shape:       {artifact['chi2_fraction_from_shape']:.6f}")
    print()
    print("  Fitted residual component, log(pred)-log(data):")
    print(f"    intercept:                    {artifact['intercept_fit_pred_minus_data']:.6f}")
    print(f"    slope in log(phiStar):        {artifact['slope_fit_pred_minus_data']:.6f}")
    print()
    print("  Slope comparison:")
    print(f"    data observed slope:          {artifact['slope_data_observed']:.6f}")
    print(f"    DASHI v4 effective slope:     {artifact['slope_dashi_v4']:.6f}")
    print(f"    correction for prediction:    {artifact['slope_correction_needed_for_prediction']:.6f}")
    print()
    if artifact["strict_pass_after_shape_removal"]:
        print("  PROMOTABILITY: numeric shape correction is sufficient; derivation still required.")
    else:
        print("  PROMOTABILITY: not sufficient; residual obstruction remains after span removal.")

    extended = artifact["extended_basis_decomposition"]
    print("\nEXTENDED BASIS DECOMPOSITION")
    for label, key in [
        ("span(1, log)", "log_linear"),
        ("span(1, log, log^2)", "log_quadratic"),
        ("span(1, log, log^2, log^3)", "log_cubic"),
    ]:
        item = extended[key]
        print(f"  {label}:")
        print(f"    basis dim:                  {item['basis_dim']}")
        print(f"    coverage rho:               {item['coverage']:.6f}")
        print(f"    chi2/dof perpendicular:     {item['chi2_perp_per_dof']:.6f}")
        print(f"    coefficients:               {item['coefficients']}")

    print("\n  Peak residual bin after log-linear removal:")
    print(f"    bin index:                  {extended['peak_residual_bin_after_linear']}")
    print(f"    phi_star:                   {extended['peak_residual_phi_star_after_linear']:.6f}")
    print(
        "    per-bin chi2 diag approx:   "
        f"{extended['peak_residual_per_bin_chi2_after_linear_diag_approx']:.6f}"
    )
    print(f"    top 5 bins:                 {extended['top_residual_bins_after_linear']}")

    print("\nPROMOTABILITY LADDER")
    for label, key in [
        ("log-linear", "log_linear"),
        ("log-quadratic", "log_quadratic"),
        ("log-cubic", "log_cubic"),
    ]:
        item = extended[key]
        status = _promotability_label(item["chi2_perp_per_dof"])
        print(f"  {label:15s} chi2/dof = {item['chi2_perp_per_dof']:10.6f}  {status}")
    print(f"\n  Artifact written: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
