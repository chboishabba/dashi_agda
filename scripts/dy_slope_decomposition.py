#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import minimize, minimize_scalar
from scipy.special import erf

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


def _sign_label(value: float) -> str:
    return "+" if value >= 0.0 else "-"


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

    window = 8
    signed_window_lo = max(0, peak_bin - window)
    signed_window_hi = min(n_bins, peak_bin + window + 1)
    signed_residual_window = []
    for index in range(signed_window_lo, signed_window_hi):
        signed_residual_window.append(
            {
                "bin": int(index),
                "phi_star": float(phi_star[index]),
                "residual_perp_after_linear": float(residual_corrected[index]),
                "sign": _sign_label(float(residual_corrected[index])),
                "per_bin_chi2_after_linear_diag_approx": float(per_bin_chi2_after_linear[index]),
            }
        )
    window_signs = np.sign(residual_corrected[signed_window_lo:signed_window_hi])
    sign_flip_offsets = np.where(np.diff(window_signs) != 0)[0]
    sign_flip_bins = [int(signed_window_lo + offset) for offset in sign_flip_offsets]

    step_basis = np.zeros_like(phi_star)
    step_basis[peak_bin:] = 1.0
    basis_step = np.column_stack([np.ones_like(log_phi), log_phi, step_basis])
    step_projection = _trbd_projection(residual_pred_minus_data, basis_step, cov_inv, chi2_raw)

    below_pivot = (phi_star < phi_star[peak_bin]).astype(float)
    above_pivot = 1.0 - below_pivot
    basis_piecewise = np.column_stack(
        [
            np.ones_like(log_phi),
            log_phi * below_pivot,
            log_phi * above_pivot,
        ]
    )
    piecewise_projection = _trbd_projection(residual_pred_minus_data, basis_piecewise, cov_inv, chi2_raw)

    if len(sign_flip_bins) >= 2:
        transition_1_bin = sign_flip_bins[0]
        transition_2_bin = sign_flip_bins[1]
    else:
        transition_1_bin = 13
        transition_2_bin = 16
    transition_1_phi = float(phi_star[transition_1_bin])
    transition_2_phi = float(phi_star[transition_2_bin])

    region_1 = (phi_star < transition_1_phi).astype(float)
    region_2 = ((phi_star >= transition_1_phi) & (phi_star < transition_2_phi)).astype(float)
    region_3 = (phi_star >= transition_2_phi).astype(float)
    basis_two_transition = np.column_stack(
        [
            region_1,
            log_phi * region_1,
            region_2,
            log_phi * region_2,
            region_3,
            log_phi * region_3,
        ]
    )
    two_transition_projection = _trbd_projection(
        residual_pred_minus_data,
        basis_two_transition,
        cov_inv,
        chi2_raw,
    )

    gaussian_width = 0.5
    gauss_log = np.exp(-0.5 * (log_phi / gaussian_width) ** 2)
    basis_sudakov = np.column_stack(
        [
            gauss_log * region_1,
            log_phi * region_2,
            region_3,
            log_phi * region_3,
        ]
    )
    sudakov_projection = _trbd_projection(
        residual_pred_minus_data,
        basis_sudakov,
        cov_inv,
        chi2_raw,
    )

    d2_pred = np.gradient(np.gradient(pred, phi_star), phi_star)
    bin_widths = np.gradient(phi_star)
    bin_integration_correction = (bin_widths**2 / 24.0) * d2_pred
    pred_bin_integrated = np.maximum(pred + bin_integration_correction, np.finfo(float).tiny)
    residual_bin_integrated = np.log(pred_bin_integrated) - log_data
    chi2_bin_integrated = float(residual_bin_integrated @ cov_inv @ residual_bin_integrated)
    chi2_bin_integrated_per_dof = chi2_bin_integrated / n_bins

    def shifted_cubic_chi2(mu: float) -> float:
        log_phi_shifted = log_phi - mu
        shifted_basis = np.column_stack(
            [
                np.ones_like(log_phi),
                log_phi_shifted,
                log_phi_shifted**2,
                log_phi_shifted**3,
            ]
        )
        try:
            shifted_projection = _trbd_projection(
                residual_pred_minus_data,
                shifted_basis,
                cov_inv,
                chi2_raw,
            )
        except np.linalg.LinAlgError:
            return 1.0e9
        return float(shifted_projection["chi2_perp_per_dof"])

    shifted_result = minimize_scalar(
        shifted_cubic_chi2,
        bounds=(-3.0, 2.0),
        method="bounded",
    )
    shifted_mu = float(shifted_result.x)
    shifted_log_phi = log_phi - shifted_mu
    shifted_cubic_basis = np.column_stack(
        [
            np.ones_like(log_phi),
            shifted_log_phi,
            shifted_log_phi**2,
            shifted_log_phi**3,
        ]
    )
    shifted_cubic_projection = _trbd_projection(
        residual_pred_minus_data,
        shifted_cubic_basis,
        cov_inv,
        chi2_raw,
    )

    def erf_basis_chi2(params: np.ndarray) -> float:
        mu = float(params[0])
        sigma = max(float(params[1]), 0.01)
        erf_component = erf((log_phi - mu) / sigma)
        erf_basis = np.column_stack(
            [
                np.ones_like(log_phi),
                log_phi,
                erf_component,
            ]
        )
        try:
            erf_projection = _trbd_projection(
                residual_pred_minus_data,
                erf_basis,
                cov_inv,
                chi2_raw,
            )
        except np.linalg.LinAlgError:
            return 1.0e9
        return float(erf_projection["chi2_perp_per_dof"])

    erf_result = minimize(
        erf_basis_chi2,
        x0=np.array([0.0, 0.5]),
        method="Nelder-Mead",
        options={"xatol": 1.0e-4, "fatol": 1.0e-4},
    )
    erf_mu = float(erf_result.x[0])
    erf_sigma = max(float(erf_result.x[1]), 0.01)
    erf_component = erf((log_phi - erf_mu) / erf_sigma)
    erf_basis = np.column_stack(
        [
            np.ones_like(log_phi),
            log_phi,
            erf_component,
        ]
    )
    erf_projection = _trbd_projection(
        residual_pred_minus_data,
        erf_basis,
        cov_inv,
        chi2_raw,
    )

    log_ratio = log_data - log_pred
    basis_multiplicative = np.column_stack(
        [
            np.ones_like(log_phi),
            log_phi,
            log_phi**2,
        ]
    )
    multiplicative_projection = _trbd_projection(
        log_ratio,
        basis_multiplicative,
        cov_inv,
        float(log_ratio @ cov_inv @ log_ratio),
    )
    multiplicative_coefficients = np.array(
        multiplicative_projection["coefficients"],
        dtype=float,
    )
    alpha_fit = np.exp(basis_multiplicative @ multiplicative_coefficients)
    pred_multiplicative_corrected = pred * alpha_fit
    residual_multiplicative_corrected = np.log(pred_multiplicative_corrected) - log_data
    chi2_multiplicative_corrected = float(
        residual_multiplicative_corrected
        @ cov_inv
        @ residual_multiplicative_corrected
    )
    chi2_multiplicative_corrected_per_dof = (
        chi2_multiplicative_corrected / n_bins
    )

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
            "signed_residual_window_after_linear": {
                "window": int(window),
                "lo": int(signed_window_lo),
                "hi_exclusive": int(signed_window_hi),
                "rows": signed_residual_window,
                "sign_flip_count": int(len(sign_flip_bins)),
                "sign_flip_bins": sign_flip_bins,
                "sign_flip_phi_star": [
                    float(phi_star[index]) for index in sign_flip_bins
                ],
            },
            "mechanism_discrimination": {
                "pivot_bin": int(peak_bin),
                "pivot_phi_star": float(phi_star[peak_bin]),
                "step_at_peak": {
                    key: value
                    for key, value in step_projection.items()
                    if key != "residual_perp"
                },
                "piecewise_log_linear_at_peak": {
                    key: value
                    for key, value in piecewise_projection.items()
                    if key != "residual_perp"
                },
                "step_promotability": _promotability_label(
                    step_projection["chi2_perp_per_dof"]
                ),
                "piecewise_log_linear_promotability": _promotability_label(
                    piecewise_projection["chi2_perp_per_dof"]
                ),
                "preferred_diagnostic_basis": (
                    "step_at_peak"
                    if step_projection["chi2_perp_per_dof"]
                    < piecewise_projection["chi2_perp_per_dof"]
                    else "piecewise_log_linear_at_peak"
                ),
            },
            "multi_transition_discrimination": {
                "transition_1_bin": int(transition_1_bin),
                "transition_1_phi_star": transition_1_phi,
                "transition_1_interpretation": (
                    "non-perturbative to perturbative resummation transition"
                ),
                "transition_2_bin": int(transition_2_bin),
                "transition_2_phi_star": transition_2_phi,
                "transition_2_interpretation": (
                    "resummation to fixed-order tail transition"
                ),
                "lobe_structure_after_linear": [
                    "positive",
                    "negative",
                    "positive",
                ],
                "piecewise_log_linear_3_region": {
                    key: value
                    for key, value in two_transition_projection.items()
                    if key != "residual_perp"
                },
                "sudakov_matched_gaussian_log_power": {
                    key: value
                    for key, value in sudakov_projection.items()
                    if key != "residual_perp"
                },
                "bin_integration_correction": {
                    "protocol": "second_derivative_point_to_bin_average_correction_in_strict_log_metric",
                    "chi2": chi2_bin_integrated,
                    "chi2_per_dof": chi2_bin_integrated_per_dof,
                    "promotability": _promotability_label(chi2_bin_integrated_per_dof),
                },
                "piecewise_promotability": _promotability_label(
                    two_transition_projection["chi2_perp_per_dof"]
                ),
                "sudakov_promotability": _promotability_label(
                    sudakov_projection["chi2_perp_per_dof"]
                ),
                "promotable_if_derived": (
                    two_transition_projection["chi2_perp_per_dof"] <= 2.0
                    or sudakov_projection["chi2_perp_per_dof"] <= 2.0
                    or chi2_bin_integrated_per_dof <= 2.0
                ),
            },
            "smooth_antisymmetric_discrimination": {
                "shifted_cubic": {
                    key: value
                    for key, value in shifted_cubic_projection.items()
                    if key != "residual_perp"
                },
                "shifted_cubic_mu_log_phi": shifted_mu,
                "shifted_cubic_pivot_phi_star": float(np.exp(shifted_mu)),
                "shifted_cubic_optimizer_success": bool(shifted_result.success),
                "shifted_cubic_improvement_vs_unshifted": (
                    cubic_projection["chi2_perp_per_dof"]
                    - shifted_cubic_projection["chi2_perp_per_dof"]
                ),
                "shifted_cubic_identifiability_note": (
                    "diagnostic pivot is not identifiable because "
                    "span(1, x-mu, (x-mu)^2, (x-mu)^3) equals "
                    "span(1, x, x^2, x^3)"
                ),
                "erf_sigmoid": {
                    key: value
                    for key, value in erf_projection.items()
                    if key != "residual_perp"
                },
                "erf_mu_log_phi": erf_mu,
                "erf_pivot_phi_star": float(np.exp(erf_mu)),
                "erf_sigma_log_phi": erf_sigma,
                "erf_optimizer_success": bool(erf_result.success),
                "multiplicative_correction": {
                    "basis": "log_ratio_quadratic_in_log_phiStar",
                    "coefficients": [
                        float(value) for value in multiplicative_coefficients
                    ],
                    "log_ratio_projection_chi2_perp_per_dof": multiplicative_projection[
                        "chi2_perp_per_dof"
                    ],
                    "chi2_after_correction": chi2_multiplicative_corrected,
                    "chi2_per_dof_after_correction": (
                        chi2_multiplicative_corrected_per_dof
                    ),
                    "max_alpha_deviation": float(np.max(np.abs(alpha_fit - 1.0))),
                    "promotability": _promotability_label(
                        chi2_multiplicative_corrected_per_dof
                    ),
                },
                "shifted_cubic_promotability": _promotability_label(
                    shifted_cubic_projection["chi2_perp_per_dof"]
                ),
                "erf_promotability": _promotability_label(
                    erf_projection["chi2_perp_per_dof"]
                ),
                "promotable_if_derived": (
                    shifted_cubic_projection["chi2_perp_per_dof"] <= 2.0
                    or erf_projection["chi2_perp_per_dof"] <= 2.0
                    or chi2_multiplicative_corrected_per_dof <= 2.0
                ),
            },
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

    signed = extended["signed_residual_window_after_linear"]
    print("\nSIGNED RESIDUAL AROUND PEAK BIN")
    print(
        "  Peak bin: "
        f"{extended['peak_residual_bin_after_linear']}  "
        f"phi_star = {extended['peak_residual_phi_star_after_linear']:.6f}"
    )
    print(f"  Window: bins {signed['lo']} to {signed['hi_exclusive'] - 1}")
    print("   bin    phi_star        r_perp   sign    per-bin chi2")
    for row in signed["rows"]:
        print(
            f"  {row['bin']:4d}  {row['phi_star']:10.6f}  "
            f"{row['residual_perp_after_linear']:12.6f}  "
            f"{row['sign']:>5s}  "
            f"{row['per_bin_chi2_after_linear_diag_approx']:14.6f}"
        )
    print(f"  Sign flips in window:         {signed['sign_flip_count']}")
    if signed["sign_flip_count"] > 0:
        print(f"  Flip bins:                    {signed['sign_flip_bins']}")
        print(f"  Flip phi_star:                {signed['sign_flip_phi_star']}")

    print("\nPROMOTABILITY LADDER")
    for label, key in [
        ("log-linear", "log_linear"),
        ("log-quadratic", "log_quadratic"),
        ("log-cubic", "log_cubic"),
    ]:
        item = extended[key]
        status = _promotability_label(item["chi2_perp_per_dof"])
        print(f"  {label:15s} chi2/dof = {item['chi2_perp_per_dof']:10.6f}  {status}")

    mechanism = extended["mechanism_discrimination"]
    print("\nMECHANISM DISCRIMINATION")
    for label, key in [
        ("log-cubic", "log_cubic"),
        ("step at peak", "step_at_peak"),
        ("piecewise log-linear", "piecewise_log_linear_at_peak"),
    ]:
        item = extended[key] if key == "log_cubic" else mechanism[key]
        status = _promotability_label(item["chi2_perp_per_dof"])
        print(f"  {label:22s} chi2/dof = {item['chi2_perp_per_dof']:10.6f}  {status}")
    print(f"  Preferred diagnostic basis:   {mechanism['preferred_diagnostic_basis']}")

    multi_transition = extended["multi_transition_discrimination"]
    print("\nMULTI-TRANSITION MECHANISM DISCRIMINATION")
    print(
        "  Transition 1: "
        f"bin {multi_transition['transition_1_bin']}  "
        f"phi_star = {multi_transition['transition_1_phi_star']:.6f}"
    )
    print(
        "  Transition 2: "
        f"bin {multi_transition['transition_2_bin']}  "
        f"phi_star = {multi_transition['transition_2_phi_star']:.6f}"
    )
    for label, key in [
        ("log-cubic compact", "log_cubic"),
        ("piecewise log-linear 3-region", "piecewise_log_linear_3_region"),
        ("Sudakov-matched", "sudakov_matched_gaussian_log_power"),
    ]:
        item = extended[key] if key == "log_cubic" else multi_transition[key]
        status = _promotability_label(item["chi2_perp_per_dof"])
        print(f"  {label:32s} chi2/dof = {item['chi2_perp_per_dof']:10.6f}  {status}")
    bin_integration = multi_transition["bin_integration_correction"]
    print(
        "  bin-integration correction      "
        f"chi2/dof = {bin_integration['chi2_per_dof']:10.6f}  "
        f"{bin_integration['promotability']}"
    )
    print(
        "  Promotable if derived:         "
        f"{multi_transition['promotable_if_derived']}"
    )

    smooth = extended["smooth_antisymmetric_discrimination"]
    print("\nSMOOTH ANTISYMMETRIC DISCRIMINATION")
    shifted = smooth["shifted_cubic"]
    print(
        "  shifted cubic pivot:          "
        f"log(phi*) = {smooth['shifted_cubic_mu_log_phi']:.6f}, "
        f"phi* = {smooth['shifted_cubic_pivot_phi_star']:.6f}"
    )
    print(
        "  shifted cubic                 "
        f"chi2/dof = {shifted['chi2_perp_per_dof']:10.6f}  "
        f"{smooth['shifted_cubic_promotability']}"
    )
    print(
        "  shifted cubic improvement:    "
        f"{smooth['shifted_cubic_improvement_vs_unshifted']:.6f}"
    )
    erf_item = smooth["erf_sigmoid"]
    print(
        "  erf pivot/width:              "
        f"log(phi*) = {smooth['erf_mu_log_phi']:.6f}, "
        f"phi* = {smooth['erf_pivot_phi_star']:.6f}, "
        f"sigma = {smooth['erf_sigma_log_phi']:.6f}"
    )
    print(
        "  erf/sigmoid                   "
        f"chi2/dof = {erf_item['chi2_perp_per_dof']:10.6f}  "
        f"{smooth['erf_promotability']}"
    )
    mult = smooth["multiplicative_correction"]
    print(
        "  multiplicative correction     "
        f"chi2/dof = {mult['chi2_per_dof_after_correction']:10.6f}  "
        f"{mult['promotability']}"
    )
    print(
        "  Promotable if derived:         "
        f"{smooth['promotable_if_derived']}"
    )
    print(f"\n  Artifact written: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
