#!/usr/bin/env python3
"""Scan shellwise cycle-family packing overlap for the active NS Wall 1 carrier.

This is candidate-only empirical telemetry. It reuses the existing triad
carrier, integer cycle-family basis, and cocycle lower-bound helpers, then
measures overlap between obstruction directions, Gram conditioning, packing
concentration, and whether the cycle-family obstruction directions collapse.

No theorem, Clay, or route-closure claim is inferred from this scan.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_triad_cocycle_floor_scan import (  # type: ignore
    AUTHORITY,
    CONTRACT as SOURCE_CONTRACT,
    DEFAULT_OUTPUT_JSON as DEFAULT_COCYCLE_FLOOR_JSON,
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_SEED,
    DEFAULT_SHELLS,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    OK_STATUS,
    PARTIAL_STATUS,
    ERROR_STATUS,
    _build_incidence,
    _build_triad_links,
    _choose_best_reference,
    _collect_modes,
    _cycle_lower_bounds,
    _fit_phase_field,
    _frame_velocity,
    _fraction,
    _integer_cycle_basis,
    _json_text,
    _load_raw_bundle,
    _mode_arrays,
    _mode_shell_filter,
    _scalar_vorticity_spectrum,
    _triadwise_oracle_target,
    _validate_shells,
    _wrap_phase,
)


SCRIPT_NAME = "scripts/ns_triad_cycle_packing_overlap_scan.py"
CONTRACT = "ns_triad_cycle_packing_overlap_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_PACKING_OVERLAP_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_packing_overlap_scan_N128_20260622.json"
)
DEFAULT_GAMMA = 1.0e-9
DEFAULT_CONDITION_THRESHOLD = 1.0e12
DEFAULT_SUPPORT_EPS = 1.0e-12
DEFAULT_OVERLAP_TOL = 1.0e-12

CONTROL_CARD = {
    "O": "Measure shellwise cycle-family packing and overlap telemetry on the active NS Wall 1 carrier.",
    "R": (
        "Build an integer cycle family, analyze support overlap and weighted Gram conditioning, "
        "and flag whether obstruction directions collapse under the shell carrier."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; the packing/overlap surface is empirical and non-promoting.",
    "L": (
        "Load raw frames, select shell carriers, build resonant triads, extract an integer cycle family, "
        "and summarize overlap, concentration, and collapse telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "The scan estimates cycle-family packing structure only; it does not prove a uniform lower bound.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument(
        "--shell",
        dest="shells",
        action="append",
        type=int,
        default=None,
        help="Shell cutoff N to evaluate; may be repeated. Defaults to 2 and 3.",
    )
    parser.add_argument("--gamma", type=float, default=DEFAULT_GAMMA)
    parser.add_argument("--condition-threshold", type=float, default=DEFAULT_CONDITION_THRESHOLD)
    parser.add_argument("--support-eps", type=float, default=DEFAULT_SUPPORT_EPS)
    parser.add_argument("--overlap-tol", type=float, default=DEFAULT_OVERLAP_TOL)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _mode_shell_filter(modes: list[Any], shell_n: int) -> list[Any]:
    if not modes:
        return []
    shell_levels = sorted({int(getattr(mode, "shell_radius", 0)) for mode in modes})
    cutoff_levels = set(shell_levels[: max(1, min(int(shell_n), len(shell_levels)))])
    return [mode for mode in modes if int(getattr(mode, "shell_radius", 0)) in cutoff_levels]


def _edge_key(u: int, v: int) -> tuple[int, int]:
    return (u, v) if u < v else (v, u)


def _weighted_quantile(values: np.ndarray, weights: np.ndarray, quantile: float) -> float:
    if len(values) == 0:
        return 0.0
    q = min(max(float(quantile), 0.0), 1.0)
    order = np.argsort(values)
    sorted_values = np.asarray(values[order], dtype=np.float64)
    sorted_weights = np.asarray(weights[order], dtype=np.float64)
    total = float(np.sum(sorted_weights))
    if total <= 0.0 or not math.isfinite(total):
        return float(sorted_values[-1])
    cutoff = q * total
    cumulative = np.cumsum(sorted_weights)
    index = int(np.searchsorted(cumulative, cutoff, side="left"))
    index = max(0, min(index, len(sorted_values) - 1))
    return float(sorted_values[index])


def _effective_rank_from_eigenvalues(eigenvalues: np.ndarray, tol: float) -> float:
    positive = np.asarray([float(v) for v in eigenvalues if float(v) > float(tol)], dtype=np.float64)
    if len(positive) == 0:
        return 0.0
    total = float(np.sum(positive))
    if total <= 0.0:
        return 0.0
    p = positive / total
    entropy = float(-np.sum(p * np.log(np.maximum(p, tol))))
    return float(math.exp(entropy))


def _support_overlap_metrics(
    family_matrix: np.ndarray,
    overlap_tol: float,
) -> dict[str, Any]:
    if family_matrix.ndim != 2 or family_matrix.size == 0:
        return {
            "family_support_overlap_mean": 0.0,
            "family_support_overlap_max": 0.0,
            "family_support_overlap_p95": 0.0,
            "family_support_overlap_density": 0.0,
            "family_support_overlap_row_mean": 0.0,
            "family_support_overlap_row_max": 0.0,
            "family_packing_concentration": 0.0,
            "family_packing_entropy_normalized": 0.0,
            "family_packing_effective_count": 0.0,
            "family_edge_usage_max": 0.0,
            "family_edge_usage_entropy_normalized": 0.0,
            "family_edge_usage_effective_count": 0.0,
            "family_support_overlap_matrix": [],
            "family_edge_usage_counts": [],
        }

    support_mask = np.abs(np.asarray(family_matrix, dtype=np.float64)) > float(overlap_tol)
    cycle_support_sizes = np.sum(support_mask, axis=1).astype(np.float64)
    if family_matrix.shape[0] == 1:
        overlap_counts = np.asarray([[float(cycle_support_sizes[0])]], dtype=np.float64)
    else:
        overlap_counts = np.asarray(support_mask.astype(np.float64) @ support_mask.astype(np.float64).T, dtype=np.float64)
    denom = np.sqrt(np.maximum(np.outer(cycle_support_sizes, cycle_support_sizes), float(overlap_tol)))
    normalized_overlap = np.divide(
        overlap_counts,
        denom,
        out=np.zeros_like(overlap_counts, dtype=np.float64),
        where=denom > 0.0,
    )

    if family_matrix.shape[0] > 1:
        off_diag = normalized_overlap[np.triu_indices(family_matrix.shape[0], k=1)]
    else:
        off_diag = np.asarray([], dtype=np.float64)
    edge_usage_counts = np.sum(support_mask, axis=0).astype(np.float64)
    total_usage = float(np.sum(edge_usage_counts))
    if total_usage > 0.0:
        usage_prob = edge_usage_counts / total_usage
        usage_entropy = float(-np.sum(usage_prob[usage_prob > 0.0] * np.log(usage_prob[usage_prob > 0.0])))
        usage_entropy_norm = float(usage_entropy / math.log(len(edge_usage_counts))) if len(edge_usage_counts) > 1 else 0.0
        usage_effective_count = float(math.exp(usage_entropy))
        packing_concentration = float(np.max(usage_prob))
    else:
        usage_entropy_norm = 0.0
        usage_effective_count = 0.0
        packing_concentration = 0.0

    row_overlap_means = np.asarray(
        [
            float(np.mean(np.delete(normalized_overlap[index], index))) if family_matrix.shape[0] > 1 else 0.0
            for index in range(family_matrix.shape[0])
        ],
        dtype=np.float64,
    )
    row_overlap_max = np.asarray(
        [
            float(np.max(np.delete(normalized_overlap[index], index))) if family_matrix.shape[0] > 1 else 0.0
            for index in range(family_matrix.shape[0])
        ],
        dtype=np.float64,
    )
    return {
        "family_support_overlap_mean": float(np.mean(off_diag)) if len(off_diag) else 0.0,
        "family_support_overlap_max": float(np.max(off_diag)) if len(off_diag) else 0.0,
        "family_support_overlap_p95": float(np.quantile(off_diag, 0.95)) if len(off_diag) else 0.0,
        "family_support_overlap_density": _fraction(float(np.count_nonzero(off_diag > float(overlap_tol))), float(len(off_diag))) if len(off_diag) else 0.0,
        "family_support_overlap_row_mean": float(np.mean(row_overlap_means)) if len(row_overlap_means) else 0.0,
        "family_support_overlap_row_max": float(np.max(row_overlap_max)) if len(row_overlap_max) else 0.0,
        "family_packing_concentration": float(packing_concentration),
        "family_packing_entropy_normalized": float(usage_entropy_norm),
        "family_packing_effective_count": float(usage_effective_count),
        "family_edge_usage_max": float(np.max(edge_usage_counts)) if len(edge_usage_counts) else 0.0,
        "family_edge_usage_entropy_normalized": float(usage_entropy_norm),
        "family_edge_usage_effective_count": float(usage_effective_count),
        "family_support_overlap_matrix": normalized_overlap.tolist(),
        "family_edge_usage_counts": edge_usage_counts.tolist(),
    }


def _family_direction_collapse(
    family_matrix: np.ndarray,
    gram_condition: float,
    condition_threshold: float,
    overlap_max: float,
    support_overlap_mean: float,
) -> tuple[bool, float, list[str]]:
    if family_matrix.ndim != 2 or family_matrix.size == 0:
        return True, 1.0, ["empty_family_matrix"]
    family_count = int(family_matrix.shape[0])
    support_tol = max(float(DEFAULT_OVERLAP_TOL), 1.0e-12)
    singular_values = np.linalg.svd(np.asarray(family_matrix, dtype=np.float64), compute_uv=False)
    effective_rank = _effective_rank_from_eigenvalues(singular_values * singular_values, support_tol)
    collapse_score = 1.0 - _fraction(effective_rank, float(max(family_count, 1)))
    reasons: list[str] = []
    if not math.isfinite(float(gram_condition)) or float(gram_condition) > float(condition_threshold):
        reasons.append("ill_conditioned_gram")
    if effective_rank <= max(1.0, 0.5 * float(family_count)):
        reasons.append("low_effective_rank")
    if overlap_max >= 0.95:
        reasons.append("high_support_overlap")
    if support_overlap_mean >= 0.50:
        reasons.append("dense_direction_overlap")
    collapsed = len(reasons) > 0
    return bool(collapsed), float(max(0.0, min(1.0, collapse_score))), reasons


def _family_basis_and_graph(
    modes: list[Any],
    triad_links: list[Any],
    zero_eps: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    amplitudes, phases, _, _ = _mode_arrays(modes)
    mode_count = len(modes)
    triad_count = len(triad_links)
    incidence = np.zeros((triad_count, mode_count), dtype=np.float64)
    weights = np.zeros(triad_count, dtype=np.float64)
    closures = np.zeros(triad_count, dtype=np.float64)
    shell_radii = np.asarray([float(mode.shell_radius) for mode in modes], dtype=np.float64)
    phases = np.asarray([float(mode.phase) for mode in modes], dtype=np.float64)
    for index, triad in enumerate(triad_links):
        left = int(triad.left)
        right = int(triad.right)
        out = int(triad.out)
        incidence[index, left] = 1.0
        incidence[index, right] = 1.0
        incidence[index, out] = -1.0
        weights[index] = float(triad.weight)
        closures[index] = float(_wrap_phase(phases[left] + phases[right] - phases[out]))

    basis = _integer_cycle_basis(incidence, zero_eps=zero_eps)
    if basis.ndim != 2:
        basis = np.zeros((0, triad_count), dtype=np.float64)

    triad_edge_weights = np.maximum(np.asarray(weights, dtype=np.float64), float(zero_eps))
    gram = (
        np.asarray(
            basis @ np.diag(1.0 / np.maximum(triad_edge_weights, float(zero_eps))) @ basis.T,
            dtype=np.float64,
        )
        if basis.size
        else np.zeros((0, 0), dtype=np.float64)
    )
    gram = 0.5 * (gram + gram.T) if gram.size else gram
    eigvals = np.linalg.eigvalsh(gram) if gram.size else np.zeros(0, dtype=np.float64)
    eig_scale = float(np.max(np.abs(eigvals))) if len(eigvals) else 0.0
    tol = max(eig_scale * 1.0e-9, 1.0e-30)
    positive = eigvals[eigvals > tol]
    gram_rank = float(len(positive))
    gram_condition = float(np.max(positive) / max(np.min(positive), tol)) if len(positive) else 0.0
    gram_effective_rank = float(_effective_rank_from_eigenvalues(eigvals, tol)) if len(eigvals) else 0.0
    reg_ridge = float(max(float(tol), float(np.max(eigvals)) * 1.0e-9 if len(eigvals) else float(tol)))
    gram_regularized = gram + reg_ridge * np.eye(gram.shape[0], dtype=np.float64) if gram.size else gram
    reg_eigvals = np.linalg.eigvalsh(gram_regularized) if gram_regularized.size else np.zeros(0, dtype=np.float64)
    reg_positive = reg_eigvals[reg_eigvals > tol]
    reg_condition = float(np.max(reg_positive) / max(np.min(reg_positive), tol)) if len(reg_positive) else 0.0
    reg_effective_rank = float(_effective_rank_from_eigenvalues(reg_eigvals, tol)) if len(reg_eigvals) else 0.0

    family_overlap_metrics = _support_overlap_metrics(basis, float(DEFAULT_OVERLAP_TOL))
    return basis, gram, gram_regularized, np.asarray(weights, dtype=np.float64), {
        "incidence": incidence,
        "closures": closures,
        "shell_radii": shell_radii,
        "family_overlap_metrics": family_overlap_metrics,
        "gram_rank": float(gram_rank),
        "gram_condition": float(gram_condition),
        "gram_effective_rank": float(gram_effective_rank),
        "gram_regularized_condition": float(reg_condition),
        "gram_regularized_effective_rank": float(reg_effective_rank),
        "gram_regularization_ridge": float(reg_ridge),
        "gram_min_eig": float(np.min(positive)) if len(positive) else 0.0,
        "gram_max_eig": float(np.max(positive)) if len(positive) else 0.0,
        "gram_regularized_min_eig": float(np.min(reg_positive)) if len(reg_positive) else 0.0,
        "gram_regularized_max_eig": float(np.max(reg_positive)) if len(reg_positive) else 0.0,
    }


def _triad_metrics_for_shell(
    shell_modes: list[Any],
    triad_links: list[Any],
    zero_eps: float,
    gamma: float,
    condition_threshold: float,
    overlap_tol: float,
    support_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    amplitudes, phases, _, shell_coord = _mode_arrays(shell_modes)
    fitted_phase, _, _, _, phase_field_fit_rmse = _fit_phase_field(shell_modes, zero_eps=zero_eps)
    best_reference, best_shift, reference_rows = _choose_best_reference(
        phases=phases,
        amplitudes=amplitudes,
        shell_coord=shell_coord,
        fitted_phase=fitted_phase,
        triad_links=triad_links,
        zero_eps=zero_eps,
    )
    oracle_target, oracle_metrics = _triadwise_oracle_target(reference_rows=reference_rows, triad_count=len(triad_links))

    incidence, weights, closures, shell_spreads, distinct_shells = _build_incidence(shell_modes, triad_links)
    family_rows, family_lower_metrics = _cycle_lower_bounds(
        incidence=incidence,
        weights=weights,
        target_cocycle=oracle_target,
        zero_eps=zero_eps,
    )
    basis = _integer_cycle_basis(incidence, zero_eps=zero_eps)
    if basis.ndim != 2:
        basis = np.zeros((0, len(triad_links)), dtype=np.float64)

    overlap_metrics = _support_overlap_metrics(basis, float(overlap_tol))
    triad_edge_weights = np.maximum(np.asarray(weights, dtype=np.float64), max(float(zero_eps), float(gamma)))
    gram = np.asarray(
        basis @ np.diag(1.0 / np.maximum(triad_edge_weights, max(float(zero_eps), float(gamma)))) @ basis.T,
        dtype=np.float64,
    ) if basis.size else np.zeros((0, 0), dtype=np.float64)
    gram = 0.5 * (gram + gram.T) if gram.size else gram
    eigvals = np.linalg.eigvalsh(gram) if gram.size else np.zeros(0, dtype=np.float64)
    tol = max(float(zero_eps) * 1000.0, 1.0e-12)
    positive = eigvals[eigvals > tol]
    gram_condition = float(np.max(positive) / max(np.min(positive), tol)) if len(positive) else 0.0
    gram_effective_rank = float(_effective_rank_from_eigenvalues(eigvals, tol)) if len(eigvals) else 0.0
    reg_ridge = float(max(float(gamma), tol))
    regularization_reasons: list[str] = []
    regularization_applied = False
    if not math.isfinite(gram_condition) or gram_condition > float(condition_threshold):
        regularization_applied = True
        regularization_reasons.append("ill_conditioned_gram")
    if len(positive) < basis.shape[0]:
        regularization_applied = True
        regularization_reasons.append("rank_deficient_gram")
    if regularization_applied and reg_ridge > float(tol):
        regularization_reasons.append("ridge_floor_applied")
    gram_regularized = gram + reg_ridge * np.eye(gram.shape[0], dtype=np.float64) if regularization_applied and gram.size else gram
    reg_eigvals = np.linalg.eigvalsh(gram_regularized) if gram_regularized.size else np.zeros(0, dtype=np.float64)
    reg_positive = reg_eigvals[reg_eigvals > tol]
    reg_condition = float(np.max(reg_positive) / max(np.min(reg_positive), tol)) if len(reg_positive) else 0.0
    reg_effective_rank = float(_effective_rank_from_eigenvalues(reg_eigvals, tol)) if len(reg_eigvals) else 0.0

    collapse, collapse_score, collapse_reasons = _family_direction_collapse(
        family_matrix=basis,
        gram_condition=reg_condition,
        condition_threshold=float(condition_threshold),
        overlap_max=float(overlap_metrics["family_support_overlap_max"]),
        support_overlap_mean=float(overlap_metrics["family_support_overlap_mean"]),
    )

    support_mask = np.abs(basis) > float(max(support_eps, overlap_tol))
    support_counts = np.sum(support_mask, axis=1).astype(np.float64) if basis.size else np.zeros(0, dtype=np.float64)
    edge_usage_counts = np.asarray(overlap_metrics["family_edge_usage_counts"], dtype=np.float64)
    total_edge_usage = float(np.sum(edge_usage_counts))
    edge_usage_prob = edge_usage_counts / total_edge_usage if total_edge_usage > 0.0 else np.zeros_like(edge_usage_counts)
    edge_usage_entropy = float(-np.sum(edge_usage_prob[edge_usage_prob > 0.0] * np.log(edge_usage_prob[edge_usage_prob > 0.0]))) if total_edge_usage > 0.0 else 0.0
    edge_usage_entropy_norm = float(edge_usage_entropy / math.log(len(edge_usage_counts))) if len(edge_usage_counts) > 1 and total_edge_usage > 0.0 else 0.0
    edge_usage_effective_count = float(math.exp(edge_usage_entropy)) if total_edge_usage > 0.0 else 0.0
    packing_concentration = float(np.max(edge_usage_prob)) if total_edge_usage > 0.0 else 0.0
    packing_entropy_norm = edge_usage_entropy_norm
    packing_effective_count = edge_usage_effective_count
    family_F_max = float(
        max(
            np.max(np.abs(oracle_target)) if len(oracle_target) else 0.0,
            np.max(np.abs(closures)) if len(closures) else 0.0,
            float(support_eps),
            float(zero_eps),
        )
    )
    normalized_support_vs_F_max = _fraction(float(family_lower_metrics.get("cycle_lower_bound_support_weighted_sum", 0.0)), max(family_F_max, float(support_eps)))
    defect_vector = (
        np.asarray(
            [_wrap_phase(float(value)) for value in (np.asarray(basis, dtype=np.float64) @ np.asarray(oracle_target, dtype=np.float64))],
            dtype=np.float64,
        )
        if basis.size and len(oracle_target)
        else np.zeros(int(basis.shape[0]) if basis.ndim == 2 else 0, dtype=np.float64)
    )
    family_joint_quadratic = 0.0
    if gram_regularized.size and len(defect_vector):
        try:
            solved = np.linalg.solve(gram_regularized, defect_vector)
            energy = float(np.dot(defect_vector, solved))
            if math.isfinite(energy) and energy > 0.0:
                family_joint_quadratic = float((4.0 / (math.pi * math.pi)) * energy)
        except np.linalg.LinAlgError:
            family_joint_quadratic = 0.0
    family_lower_bound = float(max(0.0, family_joint_quadratic))
    family_upper_proxy_raw = float(4.0 * np.sum(np.maximum(np.asarray(weights, dtype=np.float64), float(zero_eps))))
    family_upper_proxy = float(max(family_upper_proxy_raw, family_lower_bound))
    family_bound_inversion_gap = float(max(0.0, family_lower_bound - family_upper_proxy_raw))
    family_bound_inversion_detected = bool(family_bound_inversion_gap > float(zero_eps))
    family_bound_consistent = not family_bound_inversion_detected
    family_lower_bound_normalized_upper = _fraction(family_lower_bound, max(family_upper_proxy, float(support_eps)))

    family_cycle_rows: list[dict[str, Any]] = []
    family_count = int(basis.shape[0])
    support_weighted_sum = float(family_lower_metrics.get("cycle_lower_bound_support_weighted_sum", 0.0))
    support_normalized_max = float(family_lower_metrics.get("cycle_lower_bound_normalized_max", 0.0))
    for idx in range(min(family_count, 12)):
        source_row = family_rows[idx] if idx < len(family_rows) else {}
        family_cycle_rows.append(
            {
                "cycle_index": int(idx),
                "support_count": int(support_counts[idx]) if idx < len(support_counts) else 0,
                "support_fraction": float(_fraction(float(support_counts[idx]) if idx < len(support_counts) else 0.0, float(len(triad_links)))) if len(triad_links) else 0.0,
                "defect": float(source_row.get("cycle_defect", 0.0)),
                "lower_bound": float(source_row.get("cycle_lower_bound", 0.0)),
                "normalized_lower_bound": float(source_row.get("cycle_lower_bound_quadratic_normalized", 0.0)),
                "support_overlap_row_mean": float(overlap_metrics["family_support_overlap_row_mean"]),
                "support_overlap_row_max": float(overlap_metrics["family_support_overlap_row_max"]),
            }
        )

    selected_amplitudes = np.asarray(amplitudes, dtype=np.float64)
    amp_sum = float(np.sum(selected_amplitudes)) if len(selected_amplitudes) else 0.0
    mode_concentration = _fraction(float(np.max(selected_amplitudes)) if len(selected_amplitudes) else 0.0, amp_sum)
    shell_spread_mean = float(np.mean(shell_spreads)) if len(shell_spreads) else 0.0
    shell_spread_p95 = _weighted_quantile(
        np.asarray(shell_spreads, dtype=np.float64),
        np.asarray(weights, dtype=np.float64),
        0.95,
    ) if len(shell_spreads) else 0.0

    return family_cycle_rows, {
        "selected_mode_count": int(len(shell_modes)),
        "selected_mode_amplitude_sum": float(amp_sum),
        "mode_concentration_fraction": float(mode_concentration),
        "triad_count": int(len(triad_links)),
        "phase_field_fit_rmse": float(phase_field_fit_rmse),
        "best_reference_id": str(best_reference["reference_id"]) if best_reference else None,
        "best_reference_kind": str(best_reference["reference_kind"]) if best_reference else None,
        "best_reference_floor_proxy": float(best_reference["frustration_floor_proxy"]) if best_reference else 0.0,
        "best_reference_lambda_max_proxy": float(best_reference["lambda_max_proxy"]) if best_reference else 0.0,
        "oracle_reference_unique_count": int(oracle_metrics.get("oracle_reference_unique_count", 0)),
        "oracle_local_vs_global_disagreement_fraction": float(oracle_metrics.get("oracle_local_vs_global_disagreement_fraction", 0.0)),
        "oracle_target_mean_abs": float(oracle_metrics.get("oracle_target_mean_abs", 0.0)),
        "shell_spread_mean": float(shell_spread_mean),
        "shell_spread_p95": float(shell_spread_p95),
        "cycle_family_dim": float(family_lower_metrics.get("cycle_rank", 0.0)),
        "cycle_family_effective_rank": float(gram_effective_rank),
        "cycle_family_support_coverage": float(family_lower_metrics.get("cycle_independent_support_coverage", 0.0)),
        "cycle_family_defect_rms": float(family_lower_metrics.get("cycle_defect_rms", 0.0)),
        "cycle_family_defect_max": float(family_lower_metrics.get("cycle_defect_max", 0.0)),
        "cycle_family_lower_bound": float(family_lower_bound),
        "cycle_family_lower_bound_max": float(family_lower_metrics.get("cycle_lower_bound_max", 0.0)),
        "cycle_family_lower_bound_normalized_max": float(support_normalized_max),
        "cycle_family_lower_bound_normalized_upper": float(family_lower_bound_normalized_upper),
        "cycle_family_lower_bound_normalized_mean": float(family_lower_metrics.get("cycle_lower_bound_normalized_mean", 0.0)),
        "cycle_family_lower_bound_normalized_sum": float(family_lower_metrics.get("cycle_lower_bound_normalized_sum", 0.0)),
        "cycle_family_lower_bound_support_weighted_sum": float(support_weighted_sum),
        "cycle_family_lower_bound_support_over_F_max": float(_fraction(float(family_lower_metrics.get("cycle_lower_bound_max", 0.0)), max(family_F_max, float(support_eps)))),
        "cycle_family_lower_bound_joint": float(family_joint_quadratic),
        "cycle_family_lower_bound_joint_over_F_max": float(_fraction(family_joint_quadratic, max(family_F_max, float(support_eps)))),
        "cycle_family_upper_proxy_raw": float(family_upper_proxy_raw),
        "cycle_family_upper_proxy": float(family_upper_proxy),
        "cycle_family_bound_inversion_detected": bool(family_bound_inversion_detected),
        "cycle_family_bound_inversion_gap": float(family_bound_inversion_gap),
        "cycle_family_bound_consistent": bool(family_bound_consistent),
        "cycle_family_F_max": float(family_F_max),
        "cycle_family_gram_trace": float(np.trace(gram)) if gram.size else 0.0,
        "cycle_family_gram_rank": float(len(positive)),
        "cycle_family_gram_condition": float(gram_condition),
        "cycle_family_gram_effective_rank": float(gram_effective_rank),
        "cycle_family_gram_min_positive_eigenvalue": float(np.min(positive)) if len(positive) else 0.0,
        "cycle_family_gram_max_eigenvalue": float(np.max(positive)) if len(positive) else 0.0,
        "cycle_family_gram_regularized_min_eig": float(np.min(reg_positive)) if len(reg_positive) else 0.0,
        "cycle_family_gram_regularized_max_eig": float(np.max(reg_positive)) if len(reg_positive) else 0.0,
        "cycle_family_gram_regularized_condition": float(reg_condition),
        "cycle_family_gram_regularized_effective_rank": float(reg_effective_rank),
        "cycle_family_regularization_applied": bool(regularization_applied),
        "cycle_family_regularization_ridge": float(reg_ridge),
        "cycle_family_regularization_reason": list(regularization_reasons),
        "cycle_family_obstruction_collapse_reason": list(collapse_reasons),
        "cycle_family_packing_concentration": float(packing_concentration),
        "cycle_family_packing_entropy_normalized": float(packing_entropy_norm),
        "cycle_family_packing_effective_count": float(packing_effective_count),
        "cycle_family_support_overlap_mean": float(overlap_metrics["family_support_overlap_mean"]),
        "cycle_family_support_overlap_max": float(overlap_metrics["family_support_overlap_max"]),
        "cycle_family_support_overlap_p95": float(overlap_metrics["family_support_overlap_p95"]),
        "cycle_family_support_overlap_density": float(overlap_metrics["family_support_overlap_density"]),
        "cycle_family_support_overlap_row_mean": float(overlap_metrics["family_support_overlap_row_mean"]),
        "cycle_family_support_overlap_row_max": float(overlap_metrics["family_support_overlap_row_max"]),
        "cycle_family_edge_usage_max": float(overlap_metrics["family_edge_usage_max"]),
        "cycle_family_edge_usage_entropy_normalized": float(overlap_metrics["family_edge_usage_entropy_normalized"]),
        "cycle_family_edge_usage_effective_count": float(overlap_metrics["family_edge_usage_effective_count"]),
        "cycle_family_normalized_support_vs_F_max": float(normalized_support_vs_F_max),
        "cycle_family_obstruction_directions_collapsed": bool(collapse),
        "cycle_family_obstruction_collapse_score": float(collapse_score),
        "cycle_family_rows_head": family_cycle_rows,
        "cycle_family_support_overlap_matrix": overlap_metrics["family_support_overlap_matrix"],
    }


def _shell_row(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    shell_n: int,
    gamma: float,
    condition_threshold: float,
    support_eps: float,
    overlap_tol: float,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "orbit_phase": float(snapshot),
        "source": str(bundle.path),
        "shell": int(shell_n),
        "top_k": int(top_k),
        "pool_multiplier": int(pool_multiplier),
        "zero_eps": float(zero_eps),
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "route_family": "Wall 1",
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        modes = _collect_modes(
            spectrum,
            top_k=int(top_k),
            zero_eps=float(zero_eps),
            pool_multiplier=int(pool_multiplier),
        )
        shell_modes = _mode_shell_filter(modes, shell_n)
        triad_links = _build_triad_links(shell_modes, zero_eps=float(zero_eps))
        family_rows, family_metrics = _triad_metrics_for_shell(
            shell_modes=shell_modes,
            triad_links=triad_links,
            zero_eps=float(zero_eps),
            gamma=float(gamma),
            condition_threshold=float(condition_threshold),
            overlap_tol=float(overlap_tol),
            support_eps=float(support_eps),
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_triad_cycle_packing_overlap_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(family_metrics["selected_mode_count"]),
            "selected_mode_amplitude_sum": float(family_metrics["selected_mode_amplitude_sum"]),
            "mode_concentration_fraction": float(family_metrics["mode_concentration_fraction"]),
            "triad_count": int(family_metrics["triad_count"]),
            "phase_field_fit_rmse": float(family_metrics["phase_field_fit_rmse"]),
            "best_reference_id": family_metrics["best_reference_id"],
            "best_reference_kind": family_metrics["best_reference_kind"],
            "best_reference_floor_proxy": float(family_metrics["best_reference_floor_proxy"]),
            "best_reference_lambda_max_proxy": float(family_metrics["best_reference_lambda_max_proxy"]),
            "oracle_reference_unique_count": int(family_metrics["oracle_reference_unique_count"]),
            "oracle_local_vs_global_disagreement_fraction": float(family_metrics["oracle_local_vs_global_disagreement_fraction"]),
            "oracle_target_mean_abs": float(family_metrics["oracle_target_mean_abs"]),
            "shell_spread_mean": float(family_metrics["shell_spread_mean"]),
            "shell_spread_p95": float(family_metrics["shell_spread_p95"]),
            "cycle_family_dim": float(family_metrics["cycle_family_dim"]),
            "cycle_family_effective_rank": float(family_metrics["cycle_family_effective_rank"]),
            "cycle_family_support_coverage": float(family_metrics["cycle_family_support_coverage"]),
            "cycle_family_defect_rms": float(family_metrics["cycle_family_defect_rms"]),
            "cycle_family_defect_max": float(family_metrics["cycle_family_defect_max"]),
            "cycle_family_lower_bound": float(family_metrics["cycle_family_lower_bound"]),
            "cycle_family_lower_bound_max": float(family_metrics["cycle_family_lower_bound_max"]),
            "cycle_family_lower_bound_normalized_max": float(family_metrics["cycle_family_lower_bound_normalized_max"]),
            "cycle_family_lower_bound_normalized_upper": float(family_metrics["cycle_family_lower_bound_normalized_upper"]),
            "cycle_family_lower_bound_normalized_mean": float(family_metrics["cycle_family_lower_bound_normalized_mean"]),
            "cycle_family_lower_bound_normalized_sum": float(family_metrics["cycle_family_lower_bound_normalized_sum"]),
            "cycle_family_lower_bound_support_weighted_sum": float(family_metrics["cycle_family_lower_bound_support_weighted_sum"]),
            "cycle_family_lower_bound_support_over_F_max": float(family_metrics["cycle_family_lower_bound_support_over_F_max"]),
            "cycle_family_lower_bound_joint": float(family_metrics["cycle_family_lower_bound_joint"]),
            "cycle_family_lower_bound_joint_over_F_max": float(family_metrics["cycle_family_lower_bound_joint_over_F_max"]),
            "cycle_family_upper_proxy_raw": float(family_metrics["cycle_family_upper_proxy_raw"]),
            "cycle_family_upper_proxy": float(family_metrics["cycle_family_upper_proxy"]),
            "cycle_family_bound_inversion_detected": bool(family_metrics["cycle_family_bound_inversion_detected"]),
            "cycle_family_bound_inversion_gap": float(family_metrics["cycle_family_bound_inversion_gap"]),
            "cycle_family_bound_consistent": bool(family_metrics["cycle_family_bound_consistent"]),
            "cycle_family_F_max": float(family_metrics["cycle_family_F_max"]),
            "cycle_family_gram_trace": float(family_metrics["cycle_family_gram_trace"]),
            "cycle_family_gram_rank": float(family_metrics["cycle_family_gram_rank"]),
            "cycle_family_gram_condition": float(family_metrics["cycle_family_gram_condition"]),
            "cycle_family_gram_effective_rank": float(family_metrics["cycle_family_gram_effective_rank"]),
            "cycle_family_gram_min_positive_eigenvalue": float(family_metrics["cycle_family_gram_min_positive_eigenvalue"]),
            "cycle_family_gram_max_eigenvalue": float(family_metrics["cycle_family_gram_max_eigenvalue"]),
            "cycle_family_gram_regularized_min_eig": float(family_metrics["cycle_family_gram_regularized_min_eig"]),
            "cycle_family_gram_regularized_max_eig": float(family_metrics["cycle_family_gram_regularized_max_eig"]),
            "cycle_family_gram_regularized_condition": float(family_metrics["cycle_family_gram_regularized_condition"]),
            "cycle_family_gram_regularized_effective_rank": float(family_metrics["cycle_family_gram_regularized_effective_rank"]),
            "cycle_family_regularization_applied": bool(family_metrics["cycle_family_regularization_applied"]),
            "cycle_family_regularization_ridge": float(family_metrics["cycle_family_regularization_ridge"]),
            "cycle_family_regularization_reason": list(family_metrics["cycle_family_regularization_reason"]),
            "cycle_family_obstruction_collapse_reason": list(family_metrics["cycle_family_obstruction_collapse_reason"]),
            "cycle_family_packing_concentration": float(family_metrics["cycle_family_packing_concentration"]),
            "cycle_family_packing_entropy_normalized": float(family_metrics["cycle_family_packing_entropy_normalized"]),
            "cycle_family_packing_effective_count": float(family_metrics["cycle_family_packing_effective_count"]),
            "cycle_family_support_overlap_mean": float(family_metrics["cycle_family_support_overlap_mean"]),
            "cycle_family_support_overlap_max": float(family_metrics["cycle_family_support_overlap_max"]),
            "cycle_family_support_overlap_p95": float(family_metrics["cycle_family_support_overlap_p95"]),
            "cycle_family_support_overlap_density": float(family_metrics["cycle_family_support_overlap_density"]),
            "cycle_family_support_overlap_row_mean": float(family_metrics["cycle_family_support_overlap_row_mean"]),
            "cycle_family_support_overlap_row_max": float(family_metrics["cycle_family_support_overlap_row_max"]),
            "cycle_family_edge_usage_max": float(family_metrics["cycle_family_edge_usage_max"]),
            "cycle_family_edge_usage_entropy_normalized": float(family_metrics["cycle_family_edge_usage_entropy_normalized"]),
            "cycle_family_edge_usage_effective_count": float(family_metrics["cycle_family_edge_usage_effective_count"]),
            "cycle_family_normalized_support_vs_F_max": float(family_metrics["cycle_family_normalized_support_vs_F_max"]),
            "cycle_family_obstruction_directions_collapsed": bool(family_metrics["cycle_family_obstruction_directions_collapsed"]),
            "cycle_family_obstruction_collapse_score": float(family_metrics["cycle_family_obstruction_collapse_score"]),
            "cycle_family_rows_head": family_rows,
            "cycle_family_support_overlap_matrix": family_metrics["cycle_family_support_overlap_matrix"],
        }
    )

    warnings: list[str] = []
    if int(family_metrics["triad_count"]) <= 0:
        warnings.append("no resonant triads in shell carrier")
    if int(family_metrics["cycle_family_dim"]) <= 0:
        warnings.append("cycle family collapsed to zero dimension")
    if bool(family_metrics["cycle_family_regularization_applied"]):
        warnings.append("family Gram regularization applied")
    if bool(family_metrics["cycle_family_obstruction_directions_collapsed"]):
        warnings.append("cycle-family obstruction directions appear collapsed")
    if bool(family_metrics["cycle_family_bound_inversion_detected"]):
        warnings.append("cycle-family lower bound exceeded the raw upper proxy; effective upper proxy was clamped")
    if warnings:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = warnings
        return PARTIAL_STATUS, row

    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]], shells: list[int]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    partial_rows = [row for row in rows if row.get("status") == PARTIAL_STATUS]
    error_rows = [row for row in rows if row.get("status") == ERROR_STATUS]
    metric_rows = [row for row in rows if row.get("status") in {OK_STATUS, PARTIAL_STATUS}]

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in metric_rows:
            value = _finite_float(row.get(key))
            if value is not None:
                values.append(value)
        return values

    def _series_from(source_rows: list[dict[str, Any]], key: str) -> list[float]:
        values: list[float] = []
        for row in source_rows:
            value = _finite_float(row.get(key))
            if value is not None:
                values.append(value)
        return values

    def _bool_series(source_rows: list[dict[str, Any]], key: str) -> list[float]:
        values: list[float] = []
        for row in source_rows:
            value = row.get(key)
            if isinstance(value, bool):
                values.append(1.0 if value else 0.0)
        return values

    def _paired_series(x_key: str, y_key: str) -> tuple[list[float], list[float]]:
        xs: list[float] = []
        ys: list[float] = []
        for row in metric_rows:
            x_val = _finite_float(row.get(x_key))
            y_val = _finite_float(row.get(y_key))
            if x_val is None or y_val is None:
                continue
            xs.append(x_val)
            ys.append(y_val)
        return xs, ys

    return {
        "processed_rows": int(len(rows)),
        "ok_rows": int(len(ok_rows)),
        "partial_rows": int(len(partial_rows)),
        "error_rows": int(len(error_rows)),
        "shells": [int(shell) for shell in shells],
        "top_k": int(metric_rows[0]["top_k"]) if metric_rows else None,
        "pool_multiplier": int(metric_rows[0]["pool_multiplier"]) if metric_rows else None,
        "zero_eps": float(metric_rows[0]["zero_eps"]) if metric_rows else None,
        "gamma": float(metric_rows[0]["cycle_family_regularization_ridge"]) if metric_rows else None,
        "condition_threshold": float(DEFAULT_CONDITION_THRESHOLD),
        "family_dim_mean": float(np.mean(_series("cycle_family_dim"))) if _series("cycle_family_dim") else 0.0,
        "family_effective_rank_mean": float(np.mean(_series("cycle_family_effective_rank"))) if _series("cycle_family_effective_rank") else 0.0,
        "family_support_overlap_mean": float(np.mean(_series("cycle_family_support_overlap_mean"))) if _series("cycle_family_support_overlap_mean") else 0.0,
        "family_support_overlap_max_mean": float(np.mean(_series("cycle_family_support_overlap_max"))) if _series("cycle_family_support_overlap_max") else 0.0,
        "family_packing_concentration_mean": float(np.mean(_series("cycle_family_packing_concentration"))) if _series("cycle_family_packing_concentration") else 0.0,
        "family_packing_entropy_normalized_mean": float(np.mean(_series("cycle_family_packing_entropy_normalized"))) if _series("cycle_family_packing_entropy_normalized") else 0.0,
        "family_regularization_rate": _fraction(
            float(sum(1 for row in metric_rows if row.get("cycle_family_regularization_applied"))),
            float(len(metric_rows)),
        ),
        "family_gram_condition_mean": float(np.mean(_series("cycle_family_gram_condition"))) if _series("cycle_family_gram_condition") else 0.0,
        "family_gram_regularized_condition_mean": float(np.mean(_series("cycle_family_gram_regularized_condition"))) if _series("cycle_family_gram_regularized_condition") else 0.0,
        "family_gram_regularized_effective_rank_mean": float(np.mean(_series("cycle_family_gram_regularized_effective_rank"))) if _series("cycle_family_gram_regularized_effective_rank") else 0.0,
        "family_lower_bound_mean": float(np.mean(_series("cycle_family_lower_bound"))) if _series("cycle_family_lower_bound") else 0.0,
        "family_lower_bound_normalized_max_mean": float(np.mean(_series("cycle_family_lower_bound_normalized_max"))) if _series("cycle_family_lower_bound_normalized_max") else 0.0,
        "family_lower_bound_normalized_upper_mean": float(np.mean(_series_from(rows, "cycle_family_lower_bound_normalized_upper"))) if _series_from(rows, "cycle_family_lower_bound_normalized_upper") else 0.0,
        "family_lower_bound_normalized_sum_mean": float(np.mean(_series("cycle_family_lower_bound_normalized_sum"))) if _series("cycle_family_lower_bound_normalized_sum") else 0.0,
        "family_lower_bound_support_weighted_sum_mean": float(np.mean(_series("cycle_family_lower_bound_support_weighted_sum"))) if _series("cycle_family_lower_bound_support_weighted_sum") else 0.0,
        "family_F_max_mean": float(np.mean(_series("cycle_family_F_max"))) if _series("cycle_family_F_max") else 0.0,
        "family_upper_proxy_raw_mean": float(np.mean(_series_from(rows, "cycle_family_upper_proxy_raw"))) if _series_from(rows, "cycle_family_upper_proxy_raw") else 0.0,
        "family_upper_proxy_mean": float(np.mean(_series_from(rows, "cycle_family_upper_proxy"))) if _series_from(rows, "cycle_family_upper_proxy") else 0.0,
        "family_bound_inversion_rate": float(np.mean(_bool_series(rows, "cycle_family_bound_inversion_detected"))) if _bool_series(rows, "cycle_family_bound_inversion_detected") else 0.0,
        "family_bound_inversion_gap_mean": float(np.mean(_series_from(rows, "cycle_family_bound_inversion_gap"))) if _series_from(rows, "cycle_family_bound_inversion_gap") else 0.0,
        "family_bound_consistent_rate": float(np.mean(_bool_series(rows, "cycle_family_bound_consistent"))) if _bool_series(rows, "cycle_family_bound_consistent") else 0.0,
        "family_normalized_support_vs_F_max_mean": float(np.mean(_series("cycle_family_normalized_support_vs_F_max"))) if _series("cycle_family_normalized_support_vs_F_max") else 0.0,
        "family_obstruction_collapse_score_mean": float(np.mean(_series("cycle_family_obstruction_collapse_score"))) if _series("cycle_family_obstruction_collapse_score") else 0.0,
        "family_obstruction_directions_collapsed_rate": _fraction(
            float(sum(1 for row in metric_rows if row.get("cycle_family_obstruction_directions_collapsed"))),
            float(len(metric_rows)),
        ),
        "family_support_overlap_vs_packing_correlation": _pearson(
            *_paired_series("cycle_family_support_overlap_mean", "cycle_family_packing_concentration"),
        ),
        "family_overlap_vs_condition_correlation": _pearson(
            *_paired_series("cycle_family_support_overlap_max", "cycle_family_gram_regularized_condition"),
        ),
        "family_lower_bound_vs_overlap_correlation": _pearson(
            *_paired_series("cycle_family_lower_bound", "cycle_family_support_overlap_mean"),
        ),
        "family_lower_bound_vs_collapse_correlation": _pearson(
            *_paired_series("cycle_family_lower_bound", "cycle_family_obstruction_collapse_score"),
        ),
        "family_rows": rows,
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells)
    warnings: list[str] = []
    try:
        bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
        snapshots = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)
    except Exception as exc:  # noqa: BLE001
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": warnings,
            "triad_cycle_packing_overlap_rows": [],
            "aggregate": _aggregate_rows([], shells),
            "route_mode": "fail-closed",
            "fail_closed": True,
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty)
        args.output_json.write_text(text + "\n", encoding="utf-8")
        print(text)
        return 1

    if not snapshots:
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "errors": ["no frames selected for triad cycle packing overlap scan"],
            "warnings": warnings,
            "triad_cycle_packing_overlap_rows": [],
            "aggregate": _aggregate_rows([], shells),
            "route_mode": "fail-closed",
            "fail_closed": True,
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty)
        args.output_json.write_text(text + "\n", encoding="utf-8")
        print(text)
        return 1

    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    for slot, snapshot in enumerate(snapshots):
        for shell_n in shells:
            status, row = _shell_row(
                slot=slot,
                snapshot=int(snapshot),
                bundle=bundle,
                top_k=int(args.top_k),
                pool_multiplier=int(args.pool_multiplier),
                zero_eps=float(args.zero_eps),
                shell_n=int(shell_n),
                gamma=float(args.gamma),
                condition_threshold=float(args.condition_threshold),
                support_eps=float(args.support_eps),
                overlap_tol=float(args.overlap_tol),
            )
            counts[status] = counts.get(status, 0) + 1
            rows.append(row)

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "source_contract_dependency": SOURCE_CONTRACT,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "output_json": str(args.output_json),
        },
        "parameters": {
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "shells": shells,
            "gamma": float(args.gamma),
            "condition_threshold": float(args.condition_threshold),
            "support_eps": float(args.support_eps),
            "overlap_tol": float(args.overlap_tol),
            "seed": int(args.seed),
        },
        "status": OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 and counts.get(PARTIAL_STATUS, 0) == 0 else PARTIAL_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": _aggregate_rows(rows, shells),
        "triad_cycle_packing_overlap_rows": rows,
        "route_mode": "fail-closed",
        "fail_closed": True,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = _json_text(payload, args.pretty)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0 if payload["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
