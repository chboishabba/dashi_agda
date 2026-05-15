#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np
from scipy.optimize import minimize, minimize_scalar
from scipy.interpolate import interp1d
from scipy.special import erf

from run_t43_projection import T44_PATH, parse_t44


DEFAULT_INPUT = Path("scripts/data/outputs/t43_strict_log_sigma_dashi_v4_20260515.json")
DEFAULT_OUTPUT = Path("scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json")
Z_MASS_GEV = 91.2
LAMBDA_QCD_GEV = 0.2
ALPHA_S_IR_FLOOR_GEV = 1.0
SUDAKOV_A1 = 4.0 / 3.0
SUDAKOV_A2 = (67.0 / 18.0 - math.pi**2 / 6.0) * SUDAKOV_A1


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


def _alpha_s_two_loop_proxy(mu: np.ndarray | float) -> np.ndarray | float:
    mu_array = np.maximum(np.asarray(mu, dtype=float), ALPHA_S_IR_FLOOR_GEV)
    return 12.0 * math.pi / (23.0 * np.log(mu_array**2 / LAMBDA_QCD_GEV**2))


def _gamma_sudakov_nll_proxy(phi_star: np.ndarray | float) -> np.ndarray | float:
    scale = np.maximum(
        Z_MASS_GEV * np.asarray(phi_star, dtype=float),
        ALPHA_S_IR_FLOOR_GEV,
    )
    alpha_over_pi = _alpha_s_two_loop_proxy(scale) / math.pi
    return SUDAKOV_A1 * alpha_over_pi + SUDAKOV_A2 * alpha_over_pi**2


def _normalise_column(column: np.ndarray) -> np.ndarray:
    norm = float(np.sqrt(np.mean(column**2)))
    if norm <= 0.0 or not math.isfinite(norm):
        raise ValueError("cannot normalise degenerate CSS basis column")
    return column / norm


def _css_bases(
    phi_star: np.ndarray,
    phi_np: float,
    phi_fo: float,
) -> tuple[np.ndarray, np.ndarray, dict[str, float]]:
    gamma = np.asarray(_gamma_sudakov_nll_proxy(phi_star), dtype=float)
    delta_fo = 1.0 + float(_alpha_s_two_loop_proxy(Z_MASS_GEV)) / math.pi
    b_np = phi_star * np.exp(-(phi_star**2) / (phi_np**2))
    b_resumm = phi_star * (phi_star / phi_fo) ** (-gamma)
    b_fo = phi_star ** (-delta_fo)
    basis_css_shape = np.column_stack(
        [
            _normalise_column(b_np),
            _normalise_column(b_resumm),
            _normalise_column(b_fo),
        ]
    )
    raw_log_directions = np.column_stack(
        [
            np.log(np.maximum(b_np, np.finfo(float).tiny)),
            np.log(np.maximum(b_resumm, np.finfo(float).tiny)),
            np.log(np.maximum(b_fo, np.finfo(float).tiny)),
        ]
    )
    raw_log_directions = raw_log_directions - raw_log_directions.mean(axis=0)
    basis_css_log_directions = np.column_stack(
        [
            _normalise_column(raw_log_directions[:, index])
            for index in range(raw_log_directions.shape[1])
        ]
    )
    return basis_css_shape, basis_css_log_directions, {
        "phi_np": float(phi_np),
        "phi_fo": float(phi_fo),
        "z_mass_gev": Z_MASS_GEV,
        "lambda_qcd_gev": LAMBDA_QCD_GEV,
        "alpha_s_ir_floor_gev": ALPHA_S_IR_FLOOR_GEV,
        "sudakov_a1": SUDAKOV_A1,
        "sudakov_a2": SUDAKOV_A2,
        "gamma_sudakov_at_np": float(_gamma_sudakov_nll_proxy(phi_np)),
        "gamma_sudakov_at_fo": float(_gamma_sudakov_nll_proxy(phi_fo)),
        "delta_fo": float(delta_fo),
    }


def _positive_css_forward_fit(
    basis_css: np.ndarray,
    log_data: np.ndarray,
    cov_inv: np.ndarray,
) -> dict[str, Any]:
    def chi2_from_log_coeff(log_coefficients: np.ndarray) -> float:
        coefficients = np.exp(log_coefficients)
        css_shape = basis_css @ coefficients
        if np.any(~np.isfinite(css_shape)) or np.any(css_shape <= 0.0):
            return 1.0e30
        residual = np.log(css_shape) - log_data
        return float(residual @ cov_inv @ residual)

    initial_scale = float(np.exp(np.mean(log_data)))
    initial_coefficients = np.full(
        basis_css.shape[1],
        initial_scale / basis_css.shape[1],
    )
    result = minimize(
        chi2_from_log_coeff,
        np.log(initial_coefficients),
        method="L-BFGS-B",
    )
    coefficients = np.exp(result.x)
    css_shape = basis_css @ coefficients
    residual = np.log(css_shape) - log_data
    chi2 = float(residual @ cov_inv @ residual)
    dof = len(log_data) - basis_css.shape[1]
    return {
        "basis_dim": int(basis_css.shape[1]),
        "coefficients": [float(value) for value in coefficients],
        "chi2": chi2,
        "chi2_per_dof": chi2 / dof,
        "dof": int(dof),
        "optimizer_success": bool(result.success),
        "optimizer_message": str(result.message),
        "strict_log_residual_convention": "log(css_positive_shape_fit) - log(data)",
    }


def _emst_fiducial_power_correction(
    phi_star: np.ndarray,
    sigma_inclusive: np.ndarray,
    kappa: float,
) -> np.ndarray:
    dsigma_dphi = np.gradient(sigma_inclusive, phi_star)
    return kappa * (sigma_inclusive + phi_star * dsigma_dphi)


def _cms_smp_20_003_derived_kappa(selection_metadata: dict[str, Any]) -> dict[str, Any]:
    lepton_pt = selection_metadata.get("lepton_pT_min_GeV", {})
    if isinstance(lepton_pt, dict):
        pt_lead = float(lepton_pt.get("leading", selection_metadata.get("leading_lepton_pT_min_GeV", 25.0)))
        pt_sub = float(lepton_pt.get("subleading", selection_metadata.get("subleading_lepton_pT_min_GeV", 20.0)))
    else:
        pt_lead = float(selection_metadata.get("leading_lepton_pT_min_GeV", lepton_pt))
        pt_sub = float(selection_metadata.get("subleading_lepton_pT_min_GeV", 20.0))
    eta_max = float(selection_metadata.get("lepton_eta_max", 2.4))
    m_z = 91.1876
    f_eta = 1.0 - 1.0 / (math.cosh(eta_max) ** 2)
    kappa = (pt_lead / (m_z / 2.0)) ** 2 * f_eta
    return {
        "analysis": "CMS-SMP-20-003",
        "source": selection_metadata.get("fiducial_selection_source", {}),
        "lepton_pT_lead_GeV": pt_lead,
        "lepton_pT_sub_GeV": pt_sub,
        "lepton_eta_max": eta_max,
        "jet_pT_min_GeV": selection_metadata.get("jet_pT_min_GeV"),
        "jet_rapidity_abs_max": selection_metadata.get("jet_rapidity_abs_max"),
        "jet_algorithm": selection_metadata.get("jet_algorithm"),
        "jet_radius": selection_metadata.get("jet_radius"),
        "m_z_GeV": m_z,
        "f_eta": f_eta,
        "kappa_derived": kappa,
        "kappa_derivation": "EMST proxy: (pT_lead/(M_Z/2))^2 * (1 - 1/cosh^2(eta_max))",
        "zero_free_parameters": True,
    }


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


def _per_bin_edges(payload: dict[str, Any]) -> tuple[np.ndarray, np.ndarray]:
    rows = payload.get("per_bin")
    if not isinstance(rows, list) or not rows:
        raise ValueError("strict-log artifact is missing non-empty per_bin records")
    low = np.array([float(row["phiStarLow"]) for row in rows], dtype=float)
    high = np.array([float(row["phiStarHigh"]) for row in rows], dtype=float)
    if np.any(high <= low):
        raise ValueError("strict-log artifact has invalid phiStar bin edges")
    return low, high


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
    selection_metadata = payload.get("selection_metadata", {})
    if not isinstance(selection_metadata, dict):
        selection_metadata = {}
    phi_star, data, pred = _per_bin_arrays(payload)
    phi_star_low, phi_star_high = _per_bin_edges(payload)
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

    basis_css_shape, basis_css_log_directions, css_parameters = _css_bases(
        phi_star,
        transition_1_phi,
        transition_2_phi,
    )
    css_log_normal = basis_css_log_directions.T @ cov_inv @ basis_css_log_directions
    css_log_condition_number = float(np.linalg.cond(css_log_normal))
    css_residual_projection = _trbd_projection(
        residual_pred_minus_data,
        basis_css_log_directions,
        cov_inv,
        chi2_raw,
    )
    css_shape_normal = basis_css_shape.T @ cov_inv @ basis_css_shape
    css_forward_fit = _positive_css_forward_fit(
        basis_css_shape,
        log_data,
        cov_inv,
    )

    emst_kappa = _cms_smp_20_003_derived_kappa(selection_metadata)
    kappa_derived = float(emst_kappa["kappa_derived"])
    delta_fid_derived = _emst_fiducial_power_correction(
        phi_star,
        pred,
        kappa_derived,
    )
    pred_emst_derived = pred + delta_fid_derived
    emst_derived_positive = bool(np.all(pred_emst_derived > 0.0))
    if emst_derived_positive:
        residual_emst_derived = np.log(pred_emst_derived) - log_data
        chi2_emst_derived = float(residual_emst_derived @ cov_inv @ residual_emst_derived)
        chi2_emst_derived_per_dof = chi2_emst_derived / n_bins
    else:
        chi2_emst_derived = 1.0e30
        chi2_emst_derived_per_dof = 1.0e30

    def emst_kappa_chi2(kappa: float) -> float:
        delta_fid = _emst_fiducial_power_correction(phi_star, pred, kappa)
        corrected = pred + delta_fid
        if np.any(~np.isfinite(corrected)) or np.any(corrected <= 0.0):
            return 1.0e30
        residual = np.log(corrected) - log_data
        return float(residual @ cov_inv @ residual) / n_bins

    emst_fit_result = minimize_scalar(
        emst_kappa_chi2,
        bounds=(-1.0, 1.0),
        method="bounded",
    )
    kappa_fitted = float(emst_fit_result.x)
    chi2_emst_fitted = float(emst_fit_result.fun)

    d2_pred = np.gradient(np.gradient(pred, phi_star), phi_star)
    bin_widths = phi_star_high - phi_star_low
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

    covariance_eigenvalues, covariance_eigenvectors = np.linalg.eigh(log_cov)
    eigen_order = np.argsort(covariance_eigenvalues)[::-1]
    covariance_eigenvalues = covariance_eigenvalues[eigen_order]
    covariance_eigenvectors = covariance_eigenvectors[:, eigen_order]
    residual_in_eigenbasis = covariance_eigenvectors.T @ residual_pred_minus_data
    chi2_per_eigenmode = residual_in_eigenbasis**2 / covariance_eigenvalues
    cumulative_chi2_per_mode = np.cumsum(chi2_per_eigenmode)
    total_chi2_eigensum = float(cumulative_chi2_per_mode[-1])
    n_modes_90pct = int(
        np.searchsorted(cumulative_chi2_per_mode / chi2_raw, 0.90) + 1
    )
    eigen_chi2_order = np.argsort(chi2_per_eigenmode)[::-1]
    cumulative_chi2_ranked = np.cumsum(chi2_per_eigenmode[eigen_chi2_order])
    n_modes_90pct_ranked = int(
        np.searchsorted(cumulative_chi2_ranked / chi2_raw, 0.90) + 1
    )
    top_eigenmode_rows = []
    for mode in range(min(10, n_bins)):
        top_eigenmode_rows.append(
            {
                "mode": int(mode),
                "eigenvalue": float(covariance_eigenvalues[mode]),
                "chi2_contribution": float(chi2_per_eigenmode[mode]),
                "cumulative_chi2_fraction": float(
                    cumulative_chi2_per_mode[mode] / chi2_raw
                ),
            }
        )
    top_chi2_eigenmode_rows = []
    for rank, mode in enumerate(eigen_chi2_order[:10]):
        top_chi2_eigenmode_rows.append(
            {
                "rank": int(rank),
                "mode": int(mode),
                "eigenvalue": float(covariance_eigenvalues[mode]),
                "chi2_contribution": float(chi2_per_eigenmode[mode]),
                "cumulative_chi2_fraction_ranked": float(
                    cumulative_chi2_ranked[rank] / chi2_raw
                ),
            }
        )

    diag_sigma_log = np.sqrt(np.diag(log_cov))
    pulls = residual_pred_minus_data / diag_sigma_log
    sorted_by_abs_pull = np.argsort(np.abs(pulls))[::-1]
    top_pull_rows = []
    for index in sorted_by_abs_pull[:15]:
        top_pull_rows.append(
            {
                "bin": int(index),
                "phi_star": float(phi_star[index]),
                "pull": float(pulls[index]),
                "abs_pull": float(abs(pulls[index])),
            }
        )
    n_large_pulls = int(np.sum(np.abs(pulls) > 3.0))
    top5_pull_bins = [int(index) for index in sorted_by_abs_pull[:5]]
    top5_pull_mask = np.zeros(n_bins)
    top5_pull_mask[top5_pull_bins] = 1.0
    residual_top5_pull_bins = residual_pred_minus_data * top5_pull_mask
    chi2_top5_pull_bins = float(
        residual_top5_pull_bins @ cov_inv @ residual_top5_pull_bins
    )

    def kinematic_rescaled_chi2(log_scale: float) -> float:
        scale = float(np.exp(log_scale))
        phi_rescaled = phi_star * scale
        try:
            interpolator = interp1d(
                phi_rescaled,
                pred,
                bounds_error=False,
                fill_value="extrapolate",
                assume_sorted=True,
            )
            pred_rescaled = interpolator(phi_star)
        except ValueError:
            return 1.0e9
        if np.any(~np.isfinite(pred_rescaled)) or np.any(pred_rescaled <= 0.0):
            return 1.0e9
        residual_rescaled = np.log(pred_rescaled) - log_data
        return float(residual_rescaled @ cov_inv @ residual_rescaled) / n_bins

    kinematic_result = minimize_scalar(
        kinematic_rescaled_chi2,
        bounds=(-0.5, 0.5),
        method="bounded",
    )
    optimal_phi_scale = float(np.exp(kinematic_result.x))
    chi2_kinematic_rescaled = float(kinematic_result.fun)

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
            "css_resummation_basis": {
                "basis_name": "CSS_QCD_resummation_three_component",
                "basis_source": "Causal_QCD_CSS_resummation_proxy",
                "protocol": "strict_log_metric",
                "derivation_path": (
                    "CSS factorisation -> Sudakov exponent -> NLL anomalous dimension proxy"
                ),
                "transition_scales_frozen_from_sign_flips": True,
                "transition_scale_caveat": (
                    "transition locations are empirical sign-flip bins; functional form is CSS-derived proxy"
                ),
                "existing_predictor_reuse_note": (
                    "DASHI.Physics.Prediction.sigma_dashi contains HEP-R48/HEP-R49 "
                    "bin-integrated Sudakov predictor diagnostics; this pass is a "
                    "strict-log decomposition and positive-shape fit, not a replacement predictor"
                ),
                "parameters": css_parameters,
                "basis_components": [
                    "phiStar * exp(-phiStar^2 / phiStarNP^2)",
                    "phiStar * (phiStar / phiStarFO)^(-gammaSudakov(phiStar))",
                    "phiStar^(-deltaFO)",
                ],
                "residual_projection_basis_convention": (
                    "centered and RMS-normalized log component directions"
                ),
                "residual_projection_normal_matrix_condition": css_log_condition_number,
                "forward_shape_normal_matrix_condition": float(
                    np.linalg.cond(css_shape_normal)
                ),
                "residual_projection": {
                    key: value
                    for key, value in css_residual_projection.items()
                    if key != "residual_perp"
                },
                "forward_positive_shape_fit": css_forward_fit,
                "residual_projection_promotability": _promotability_label(
                    css_residual_projection["chi2_perp_per_dof"]
                ),
                "forward_fit_promotability": _promotability_label(
                    css_forward_fit["chi2_per_dof"]
                ),
                "promotable_if_derived": css_forward_fit["chi2_per_dof"] <= 2.0,
            },
            "emst_fiducial_power_correction": {
                "reference": "arXiv:2006.11382",
                "correction_type": "fiducial_power_correction_proxy",
                "basis_source": "Causal_QCD_EMST_CMS_SMP_20_003",
                "strict_log_metric": True,
                "residual_convention": "log(prediction_with_emst_correction) - log(data)",
                "cms_cuts": emst_kappa,
                "derived_kappa": kappa_derived,
                "derived_delta_min": float(np.min(delta_fid_derived)),
                "derived_delta_max": float(np.max(delta_fid_derived)),
                "derived_prediction_positive": emst_derived_positive,
                "chi2_derived_kappa": chi2_emst_derived,
                "chi2_per_dof_derived_kappa": chi2_emst_derived_per_dof,
                "promotability_derived_kappa": _promotability_label(
                    chi2_emst_derived_per_dof
                ),
                "fitted_kappa_diagnostic": {
                    "kappa": kappa_fitted,
                    "chi2_per_dof": chi2_emst_fitted,
                    "optimizer_success": bool(emst_fit_result.success),
                    "optimizer_message": str(emst_fit_result.message),
                    "diagnostic_only": True,
                },
                "kappa_distance_fit_minus_derived": kappa_fitted - kappa_derived,
                "central_acceptance_A_status": selection_metadata.get(
                    "central_acceptance_A",
                    "MISSING",
                ),
                "surface_status": (
                    "derived_scalar_kappa_only; central A(M,phi*) and full "
                    "EMST fiducial surface remain missing"
                ),
                "zero_free_parameter_promotable": chi2_emst_derived_per_dof <= 2.0,
                "promotion_boundary": (
                    "derived scalar kappa is not the full fiducial correction "
                    "surface; do not promote unless strict threshold passes and "
                    "the acceptance surface contract is complete"
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
            "covariance_bin_kinematic_diagnostics": {
                "protocol": "strict_log_metric",
                "total_chi2_direct": chi2_raw,
                "total_chi2_eigensum": total_chi2_eigensum,
                "n_modes_90pct_chi2_eigenvalue_order": n_modes_90pct,
                "n_modes_90pct_chi2_ranked_by_contribution": n_modes_90pct_ranked,
                "top_eigenmode_rows": top_eigenmode_rows,
                "top_chi2_eigenmode_rows": top_chi2_eigenmode_rows,
                "top_pull_rows": top_pull_rows,
                "n_large_pulls_abs_gt_3": n_large_pulls,
                "top5_pull_bins": top5_pull_bins,
                "chi2_top5_pull_bins": chi2_top5_pull_bins,
                "chi2_fraction_top5_pull_bins": chi2_top5_pull_bins / chi2_raw,
                "kinematic_rescaling": {
                    "optimal_phi_star_scale": optimal_phi_scale,
                    "log_scale": float(kinematic_result.x),
                    "chi2_per_dof": chi2_kinematic_rescaled,
                    "scale_deviation_from_one": abs(optimal_phi_scale - 1.0),
                    "optimizer_success": bool(kinematic_result.success),
                    "promotability": _promotability_label(
                        chi2_kinematic_rescaled
                    ),
                    "diagnostic_limitations": [
                        "prediction is interpolated as point values, not re-integrated over bins",
                        "covariance remains tied to the original binning",
                        "artifact has bin edges but no continuous prediction spectrum",
                    ],
                },
                "branch_assessment": (
                    "covariance_eigenstructure_obstruction"
                    if n_modes_90pct_ranked <= 3
                    else "discrete_bin_obstruction"
                    if n_large_pulls <= 5
                    else "kinematic_convention_mismatch"
                    if chi2_kinematic_rescaled < 10.0
                    else "distributed_theoretical_model_gap"
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

    css = extended["css_resummation_basis"]
    print("\nCSS RESUMMATION BASIS")
    print(f"  Basis source:                 {css['basis_source']}")
    print(
        "  Transition scales:            "
        f"phi*_NP = {css['parameters']['phi_np']:.6f}, "
        f"phi*_FO = {css['parameters']['phi_fo']:.6f}"
    )
    print(
        "  gamma at transitions:         "
        f"{css['parameters']['gamma_sudakov_at_np']:.6f}, "
        f"{css['parameters']['gamma_sudakov_at_fo']:.6f}"
    )
    print(f"  fixed-order delta:            {css['parameters']['delta_fo']:.6f}")
    css_projection = css["residual_projection"]
    css_forward = css["forward_positive_shape_fit"]
    print(
        "  residual projection           "
        f"chi2/dof = {css_projection['chi2_perp_per_dof']:10.6f}  "
        f"{css['residual_projection_promotability']}"
    )
    print(
        "  positive forward shape fit     "
        f"chi2/dof = {css_forward['chi2_per_dof']:10.6f}  "
        f"{css['forward_fit_promotability']}"
    )
    print(f"  forward coefficients:         {css_forward['coefficients']}")
    print(
        "  Promotable if derived:         "
        f"{css['promotable_if_derived']}"
    )

    emst = extended["emst_fiducial_power_correction"]
    print("\nEMST FIDUCIAL POWER CORRECTION")
    print(f"  Reference:                    {emst['reference']}")
    print(f"  Basis source:                 {emst['basis_source']}")
    print(f"  derived kappa:                {emst['derived_kappa']:.6f}")
    print(f"  f(eta):                       {emst['cms_cuts']['f_eta']:.6f}")
    print(
        "  derived kappa chi2/dof:       "
        f"{emst['chi2_per_dof_derived_kappa']:10.6f}  "
        f"{emst['promotability_derived_kappa']}"
    )
    print(
        "  fitted kappa diagnostic:      "
        f"{emst['fitted_kappa_diagnostic']['kappa']:.6f}  "
        f"chi2/dof = {emst['fitted_kappa_diagnostic']['chi2_per_dof']:10.6f}"
    )
    print(
        "  fit-derived kappa distance:   "
        f"{emst['kappa_distance_fit_minus_derived']:.6f}"
    )
    print(f"  surface status:               {emst['surface_status']}")
    print(
        "  zero-free-param promotable:   "
        f"{emst['zero_free_parameter_promotable']}"
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

    cov_diag = extended["covariance_bin_kinematic_diagnostics"]
    print("\nCOVARIANCE, BIN, AND KINEMATIC DIAGNOSTICS")
    print(f"  Total chi2 direct:            {cov_diag['total_chi2_direct']:.6f}")
    print(f"  Total chi2 eigensum:          {cov_diag['total_chi2_eigensum']:.6f}")
    print(
        "  Modes for 90 pct chi2:        "
        f"{cov_diag['n_modes_90pct_chi2_ranked_by_contribution']} "
        "(ranked by contribution)"
    )
    print(
        "  Modes for 90 pct chi2:        "
        f"{cov_diag['n_modes_90pct_chi2_eigenvalue_order']} "
        "(eigenvalue order)"
    )
    print("  Top eigenmodes by eigenvalue:")
    print("   mode      eigenvalue      chi2_contrib    cumul_frac")
    for row in cov_diag["top_eigenmode_rows"]:
        print(
            f"  {row['mode']:5d}  "
            f"{row['eigenvalue']:14.6e}  "
            f"{row['chi2_contribution']:14.6f}  "
            f"{row['cumulative_chi2_fraction']:12.6f}"
        )
    print("  Top eigenmodes by chi2 contribution:")
    print("   rank   mode      eigenvalue      chi2_contrib    cumul_frac")
    for row in cov_diag["top_chi2_eigenmode_rows"]:
        print(
            f"  {row['rank']:5d}  "
            f"{row['mode']:5d}  "
            f"{row['eigenvalue']:14.6e}  "
            f"{row['chi2_contribution']:14.6f}  "
            f"{row['cumulative_chi2_fraction_ranked']:12.6f}"
        )
    print("  Top pull bins:")
    print("    bin    phi_star        pull      abs_pull")
    for row in cov_diag["top_pull_rows"]:
        print(
            f"  {row['bin']:5d}  "
            f"{row['phi_star']:10.6f}  "
            f"{row['pull']:10.6f}  "
            f"{row['abs_pull']:10.6f}"
        )
    print(f"  Bins with |pull| > 3:         {cov_diag['n_large_pulls_abs_gt_3']}")
    print(
        "  chi2 fraction top-5 pulls:    "
        f"{cov_diag['chi2_fraction_top5_pull_bins']:.6f}"
    )
    kin = cov_diag["kinematic_rescaling"]
    print(
        "  kinematic phi* scale:         "
        f"{kin['optimal_phi_star_scale']:.6f}"
    )
    print(
        "  kinematic rescaled chi2/dof:  "
        f"{kin['chi2_per_dof']:.6f}  {kin['promotability']}"
    )
    print(f"  Branch assessment:            {cov_diag['branch_assessment']}")
    print(f"\n  Artifact written: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
