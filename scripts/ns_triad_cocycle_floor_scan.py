#!/usr/bin/env python3
"""Scan cocycle-frustration floor proxies for the active NS triad Wall 1 route."""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_low_frustration_basin_scan import (  # type: ignore
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_SEED,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    _build_triad_links,
    _collect_modes,
    _fit_phase_field,
    _frame_velocity,
    _fraction,
    _load_raw_bundle,
    _mode_arrays,
    _reference_shift,
    _reference_specs,
    _score_shift_batch,
    _scalar_vorticity_spectrum,
    _wrap_phase_array,
)


SCRIPT_NAME = "scripts/ns_triad_cocycle_floor_scan.py"
CONTRACT = "ns_triad_cocycle_floor_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_COCYCLE_FLOOR_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cocycle_floor_scan_N128_20260621.json"
)
DEFAULT_SHELLS = (2, 3)

CONTROL_CARD = {
    "O": "Measure cocycle-frustration floor telemetry for the active NS triad Wall 1 route.",
    "R": (
        "Construct finite resonant triad incidence carriers on small shells, identify low-frustration references, "
        "and summarize cycle-defect lower-bound proxies together with irreducible floor ratios."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; cycle-defect lower bounds and floor ratios are empirical and non-promoting.",
    "L": (
        "Load raw frames, select dominant modes, form resonant triads, build an incidence operator, "
        "extract nullspace-style cycle directions, and emit floor-style telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "The scan estimates cocycle defects and floor proxies only; it does not prove a uniform lower bound.",
}

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
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
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _validate_shells(shells: list[int] | None) -> list[int]:
    values = list(DEFAULT_SHELLS if shells is None else shells)
    if not values:
        raise SystemExit("--shell must be provided at least once or left at the default shell set")
    normalized: list[int] = []
    for shell in values:
        if isinstance(shell, bool) or int(shell) <= 0:
            raise SystemExit("--shell values must be positive integers")
        normalized.append(int(shell))
    return sorted(set(normalized))


def _mode_shell_filter(modes: list[Any], shell_n: int) -> list[Any]:
    if not modes:
        return []
    shell_levels = sorted({int(getattr(mode, "shell_radius", 0)) for mode in modes})
    cutoff_levels = set(shell_levels[: max(1, min(int(shell_n), len(shell_levels)))])
    return [mode for mode in modes if int(getattr(mode, "shell_radius", 0)) in cutoff_levels]


def _build_incidence(
    modes: list[Any],
    triad_links: list[Any],
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    mode_count = len(modes)
    triad_count = len(triad_links)
    incidence = np.zeros((triad_count, mode_count), dtype=np.float64)
    weights = np.zeros(triad_count, dtype=np.float64)
    closures = np.zeros(triad_count, dtype=np.float64)
    shell_spreads = np.zeros(triad_count, dtype=np.float64)
    distinct_shells = np.zeros(triad_count, dtype=np.float64)
    phases = np.asarray([float(mode.phase) for mode in modes], dtype=np.float64)
    shell_radii = np.asarray([float(mode.shell_radius) for mode in modes], dtype=np.float64)

    for index, triad in enumerate(triad_links):
        left = int(triad.left)
        right = int(triad.right)
        out = int(triad.out)
        incidence[index, left] = 1.0
        incidence[index, right] = 1.0
        incidence[index, out] = -1.0
        weights[index] = float(triad.weight)
        closures[index] = float(_wrap_phase_array(phases[left] + phases[right] - phases[out]))
        shell_spreads[index] = float(triad.shell_spread)
        distinct_shells[index] = float(
            len({int(shell_radii[left]), int(shell_radii[right]), int(shell_radii[out])})
        )
    return incidence, weights, closures, shell_spreads, distinct_shells


def _empty_cycle_metrics(triad_count: int, mode_count: int) -> dict[str, float]:
    return {
        "cycle_rank": 0.0,
        "independent_cycle_count": 0.0,
        "cycle_basis_dim": 0.0,
        "cycle_basis_support_mean": 0.0,
        "cycle_basis_support_max": 0.0,
        "cycle_basis_support_fraction_mean": 0.0,
        "cycle_basis_weight_fraction_mean": 0.0,
        "cycle_basis_effective_support_mean": 0.0,
        "cycle_basis_dual_norm_mean": 0.0,
        "cycle_basis_dual_norm_max": 0.0,
        "cycle_defect_mean": 0.0,
        "cycle_defect_rms": 0.0,
        "cycle_defect_max": 0.0,
        "cycle_defect_density_mean": 0.0,
        "cycle_defect_per_support_mean": 0.0,
        "cycle_lower_bound_max": 0.0,
        "mean_cycle_lower_bound": 0.0,
        "cycle_lower_bound_sum": 0.0,
        "cycle_lower_bound_normalized_max": 0.0,
        "cycle_lower_bound_normalized_mean": 0.0,
        "cycle_lower_bound_normalized_sum": 0.0,
        "cycle_lower_bound_surface_sum": 0.0,
        "cycle_lower_bound_surface_density": 0.0,
        "cycle_lower_bound_support_weighted_sum": 0.0,
        "cycle_projection_energy": 0.0,
        "cycle_projection_energy_fraction": 0.0,
        "cycle_independent_support_coverage": 0.0,
        "cycle_significant_count": 0.0,
        "defective_cycle_count": 0.0,
        "cocycle_defect_mean": 0.0,
        "cocycle_defect_max": 0.0,
        "max_cycle_lower_bound": 0.0,
        "triad_count": float(triad_count),
        "mode_count": float(mode_count),
    }


def _wrap_phase(angle: float) -> float:
    wrapped = (float(angle) + math.pi) % (2.0 * math.pi) - math.pi
    if wrapped <= -math.pi:
        wrapped += 2.0 * math.pi
    return float(wrapped)


def _gcd_pair(a: int, b: int) -> int:
    a = abs(int(a))
    b = abs(int(b))
    while b:
        a, b = b, a % b
    return a


def _lcm_pair(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return abs(a * b) // _gcd_pair(a, b)


def _normalize_integer_cycle(vector: list[int]) -> list[int]:
    if not vector:
        return vector
    gcd = 0
    for value in vector:
        gcd = _gcd_pair(gcd, value)
    if gcd > 1:
        vector = [int(value // gcd) for value in vector]
    for value in vector:
        if value < 0:
            return [-entry for entry in vector]
        if value > 0:
            break
    return vector


def _integer_cycle_basis(incidence: np.ndarray, zero_eps: float) -> np.ndarray:
    if incidence.ndim != 2 or incidence.size == 0:
        return np.zeros((0, 0), dtype=np.float64)

    matrix = incidence.T
    rows = int(matrix.shape[0])
    cols = int(matrix.shape[1])
    tableau: list[list[Fraction]] = [
        [Fraction(int(round(float(matrix[row, col]))), 1) for col in range(cols)]
        for row in range(rows)
    ]

    pivot_cols: list[int] = []
    pivot_row = 0
    for col in range(cols):
        pivot = None
        for row in range(pivot_row, rows):
            if tableau[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue
        tableau[pivot_row], tableau[pivot] = tableau[pivot], tableau[pivot_row]
        pivot_value = tableau[pivot_row][col]
        tableau[pivot_row] = [value / pivot_value for value in tableau[pivot_row]]
        for row in range(rows):
            if row == pivot_row:
                continue
            factor = tableau[row][col]
            if factor == 0:
                continue
            tableau[row] = [
                current - factor * pivot_entry
                for current, pivot_entry in zip(tableau[row], tableau[pivot_row])
            ]
        pivot_cols.append(col)
        pivot_row += 1
        if pivot_row >= rows:
            break

    free_cols = [col for col in range(cols) if col not in pivot_cols]
    if not free_cols:
        return np.zeros((0, cols), dtype=np.float64)

    basis: list[list[int]] = []
    for free_col in free_cols:
        vector = [Fraction(0, 1) for _ in range(cols)]
        vector[free_col] = Fraction(1, 1)
        for row_index, pivot_col in enumerate(pivot_cols):
            vector[pivot_col] = -tableau[row_index][free_col]

        denominator_lcm = 1
        for value in vector:
            denominator_lcm = _lcm_pair(denominator_lcm, int(value.denominator))
        if denominator_lcm <= 0:
            denominator_lcm = 1
        integer_vector = [int(value * denominator_lcm) for value in vector]
        integer_vector = _normalize_integer_cycle(integer_vector)
        if any(abs(entry) > 0 for entry in integer_vector):
            basis.append(integer_vector)

    if not basis:
        return np.zeros((0, cols), dtype=np.float64)
    return np.asarray(basis, dtype=np.float64)


def _choose_best_reference(
    phases: np.ndarray,
    amplitudes: np.ndarray,
    shell_coord: np.ndarray,
    fitted_phase: np.ndarray,
    triad_links: list[Any],
    zero_eps: float,
) -> tuple[dict[str, Any], np.ndarray, list[dict[str, Any]]]:
    if len(triad_links) == 0 or len(phases) == 0:
        empty_shift = np.zeros_like(phases, dtype=np.float64)
        best = {
            "reference_id": "zero",
            "reference_kind": "global",
            "phase_slope": 0.0,
            "phase_offset": 0.0,
            "frustration_floor_proxy": 0.0,
            "frustration_floor_rmse": 0.0,
            "lambda_max_proxy": 0.0,
            "triad_phase_alignment_fraction": 0.0,
        }
        return best, empty_shift, []
    left_idx = np.asarray([int(link.left) for link in triad_links], dtype=np.int64)
    right_idx = np.asarray([int(link.right) for link in triad_links], dtype=np.int64)
    out_idx = np.asarray([int(link.out) for link in triad_links], dtype=np.int64)
    weights = np.asarray([float(link.weight) for link in triad_links], dtype=np.float64)
    rows: list[dict[str, Any]] = []

    for spec in _reference_specs():
        offset, shift = _reference_shift(
            spec=spec,
            phases=phases,
            amplitudes=amplitudes,
            shell_coord=shell_coord,
            fitted_phase=fitted_phase,
        )
        scores = _score_shift_batch(
            phases=phases,
            shifts=np.asarray(shift, dtype=np.float64),
            left_idx=left_idx,
            right_idx=right_idx,
            out_idx=out_idx,
            weights=weights,
            zero_eps=zero_eps,
        )
        residual_abs = np.asarray(scores["residual_abs"][0], dtype=np.float64)
        target_cocycle = np.asarray(
            _wrap_phase_array(
                np.asarray(shift, dtype=np.float64)[left_idx]
                + np.asarray(shift, dtype=np.float64)[right_idx]
                - np.asarray(shift, dtype=np.float64)[out_idx]
            ),
            dtype=np.float64,
        )
        rows.append(
            {
                "reference_id": spec.reference_id,
                "reference_kind": spec.reference_kind,
                "phase_slope": float(spec.phase_slope),
                "phase_offset": float(_wrap_phase(float(offset))),
                "frustration_floor_proxy": float(scores["score_mean_abs"][0]),
                "frustration_floor_rmse": float(scores["score_rmse"][0]),
                "lambda_max_proxy": float(scores["score_coherence"][0]),
                "triad_phase_alignment_fraction": float(scores["score_alignment_fraction"][0]),
                "shift": np.asarray(shift, dtype=np.float64),
                "triad_residual_abs": residual_abs,
                "target_cocycle": target_cocycle,
            }
        )

    rows.sort(
        key=lambda row: (
            float(row["frustration_floor_proxy"]),
            -float(row["lambda_max_proxy"]),
            abs(float(row["phase_slope"])),
        )
    )
    best = dict(rows[0])
    shift = np.asarray(best.pop("shift"), dtype=np.float64)
    return best, shift, rows


def _triadwise_oracle_target(
    reference_rows: list[dict[str, Any]],
    triad_count: int,
) -> tuple[np.ndarray, dict[str, Any]]:
    if triad_count <= 0 or not reference_rows:
        return np.zeros(0, dtype=np.float64), {
            "oracle_reference_unique_count": 0,
            "oracle_local_vs_global_disagreement_fraction": 0.0,
            "oracle_reference_switch_fraction": 0.0,
            "oracle_target_mean_abs": 0.0,
            "oracle_target_rms": 0.0,
            "oracle_reference_head": [],
        }

    residual_matrix = np.asarray(
        [np.asarray(row["triad_residual_abs"], dtype=np.float64) for row in reference_rows],
        dtype=np.float64,
    )
    target_matrix = np.asarray(
        [np.asarray(row["target_cocycle"], dtype=np.float64) for row in reference_rows],
        dtype=np.float64,
    )
    chosen_index = np.argmin(residual_matrix, axis=0)
    global_best_index = 0
    oracle_target = target_matrix[chosen_index, np.arange(triad_count)]
    unique_indices = sorted({int(index) for index in chosen_index.tolist()})
    reference_ids = [str(row["reference_id"]) for row in reference_rows]
    switch_fraction = _fraction(
        float(np.count_nonzero(chosen_index != global_best_index)),
        float(triad_count),
    )
    return np.asarray(_wrap_phase_array(oracle_target), dtype=np.float64), {
        "oracle_reference_unique_count": int(len(unique_indices)),
        "oracle_local_vs_global_disagreement_fraction": float(switch_fraction),
        "oracle_reference_switch_fraction": float(switch_fraction),
        "oracle_target_mean_abs": float(np.mean(np.abs(oracle_target))) if triad_count > 0 else 0.0,
        "oracle_target_rms": float(np.sqrt(np.mean(np.asarray(oracle_target, dtype=np.float64) ** 2)))
        if triad_count > 0
        else 0.0,
        "oracle_reference_head": [reference_ids[index] for index in unique_indices[: min(8, len(unique_indices))]],
    }


def _cycle_lower_bounds(
    incidence: np.ndarray,
    weights: np.ndarray,
    target_cocycle: np.ndarray,
    zero_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, float]]:
    triad_count = int(len(weights))
    mode_count = int(incidence.shape[1]) if incidence.ndim == 2 else 0
    if triad_count == 0 or incidence.size == 0:
        return [], _empty_cycle_metrics(triad_count, mode_count)

    try:
        basis = _integer_cycle_basis(incidence, zero_eps=zero_eps)
    except (ArithmeticError, ValueError, ZeroDivisionError):
        return [], _empty_cycle_metrics(triad_count, mode_count)

    nullity = int(basis.shape[0]) if basis.ndim == 2 else 0
    if nullity <= 0:
        return [], _empty_cycle_metrics(triad_count, mode_count)

    safe_weights = np.maximum(np.asarray(weights, dtype=np.float64), float(zero_eps))
    normalized_weights = safe_weights / max(float(np.sum(safe_weights)), float(zero_eps))
    safe_target_cocycle = np.asarray(target_cocycle, dtype=np.float64)
    total_weight = float(np.sum(safe_weights))
    total_defect_energy = float(np.sum(safe_target_cocycle * safe_target_cocycle))
    support_tol = max(float(zero_eps) * 1000.0, 1.0e-10)
    records: list[dict[str, Any]] = []
    lower_bounds: list[float] = []
    defects: list[float] = []
    dual_norms: list[float] = []
    support_counts: list[float] = []
    support_fractions: list[float] = []
    support_weights: list[float] = []
    support_weight_fractions: list[float] = []
    effective_supports: list[float] = []
    defect_densities: list[float] = []
    defect_per_supports: list[float] = []
    lower_bound_support_weighted: list[float] = []
    lower_bound_quadratic: list[float] = []
    lower_bound_normalized: list[float] = []
    projection_coeffs: list[float] = []
    support_union = np.zeros(triad_count, dtype=bool)

    for cycle_index, vector in enumerate(basis):
        coeffs = np.asarray(vector, dtype=np.float64)
        l2_norm = float(np.linalg.norm(coeffs))
        l1_norm = float(np.sum(np.abs(coeffs)))
        support_mask = np.abs(coeffs) > support_tol
        support_count = float(np.count_nonzero(support_mask))
        support_fraction = _fraction(support_count, float(triad_count))
        support_weight = float(np.sum(safe_weights[support_mask])) if np.any(support_mask) else 0.0
        support_weight_fraction = _fraction(support_weight, total_weight)
        effective_support = _fraction(l1_norm * l1_norm, max(l2_norm * l2_norm, float(zero_eps)))
        dual_norm_sq = float(np.sum((coeffs * coeffs) / safe_weights))
        normalized_dual_norm_sq = float(np.sum((coeffs * coeffs) / np.maximum(normalized_weights, float(zero_eps))))
        dual_norm = float(math.sqrt(max(dual_norm_sq, 0.0)))
        raw_defect = float(np.dot(coeffs, safe_target_cocycle))
        defect = abs(_wrap_phase(raw_defect))
        defect_density = _fraction(defect, max(l1_norm, float(zero_eps)))
        defect_per_support = _fraction(defect, max(support_count, 1.0))
        lower_bound_quad = 0.0
        if dual_norm_sq > float(zero_eps):
            lower_bound_quad = float((4.0 / (math.pi * math.pi)) * (defect * defect) / dual_norm_sq)
        lower_bound_quad_normalized = 0.0
        if normalized_dual_norm_sq > float(zero_eps):
            lower_bound_quad_normalized = float(
                (4.0 / (math.pi * math.pi)) * (defect * defect) / normalized_dual_norm_sq
            )
        lower_bound_support = float(_fraction(defect * support_weight_fraction, max(dual_norm, float(zero_eps))))
        lower_bound_energy = float(
            _fraction(defect * defect * support_weight_fraction, max(dual_norm_sq, float(zero_eps)))
        )
        lower_bound = max(lower_bound_quad, lower_bound_support, lower_bound_energy)
        support_union |= support_mask
        records.append(
            {
                "cycle_index": int(cycle_index),
                "cycle_support_count": int(support_count),
                "cycle_support_fraction": float(support_fraction),
                "cycle_support_weight": float(support_weight),
                "cycle_support_weight_fraction": float(support_weight_fraction),
                "cycle_effective_support": float(effective_support),
                "cycle_l1_norm": float(l1_norm),
                "cycle_l2_norm": float(l2_norm),
                "cycle_dual_norm": float(dual_norm),
                "cycle_dual_norm_sq": float(dual_norm_sq),
                "cycle_normalized_dual_norm_sq": float(normalized_dual_norm_sq),
                "cycle_raw_defect": float(raw_defect),
                "cycle_defect": float(defect),
                "cycle_defect_density": float(defect_density),
                "cycle_defect_per_support": float(defect_per_support),
                "cycle_lower_bound_quadratic": float(lower_bound_quad),
                "cycle_lower_bound_quadratic_normalized": float(lower_bound_quad_normalized),
                "cycle_lower_bound_support_weighted": float(lower_bound_support),
                "cycle_lower_bound_energy_weighted": float(lower_bound_energy),
                "cycle_lower_bound": float(lower_bound),
            }
        )
        lower_bounds.append(float(lower_bound))
        defects.append(float(defect))
        dual_norms.append(float(dual_norm))
        support_counts.append(float(support_count))
        support_fractions.append(float(support_fraction))
        support_weights.append(float(support_weight))
        support_weight_fractions.append(float(support_weight_fraction))
        effective_supports.append(float(effective_support))
        defect_densities.append(float(defect_density))
        defect_per_supports.append(float(defect_per_support))
        lower_bound_support_weighted.append(float(lower_bound_support))
        lower_bound_quadratic.append(float(lower_bound_quad))
        lower_bound_normalized.append(float(lower_bound_quad_normalized))
        projection_coeffs.append(float(raw_defect))

    defective_count = sum(1 for value in defects if value > float(zero_eps))
    projection_energy = float(np.sum(np.asarray(projection_coeffs, dtype=np.float64) ** 2))
    projection_energy_fraction = _fraction(projection_energy, max(total_defect_energy, float(zero_eps)))
    return records, {
        "cycle_rank": float(nullity),
        "independent_cycle_count": float(nullity),
        "cycle_basis_dim": float(nullity),
        "cycle_basis_support_mean": float(np.mean(support_counts)) if support_counts else 0.0,
        "cycle_basis_support_max": float(max(support_counts, default=0.0)),
        "cycle_basis_support_fraction_mean": float(np.mean(support_fractions)) if support_fractions else 0.0,
        "cycle_basis_weight_fraction_mean": float(np.mean(support_weight_fractions)) if support_weight_fractions else 0.0,
        "cycle_basis_effective_support_mean": float(np.mean(effective_supports)) if effective_supports else 0.0,
        "cycle_basis_dual_norm_mean": float(np.mean(dual_norms)) if dual_norms else 0.0,
        "cycle_basis_dual_norm_max": float(max(dual_norms, default=0.0)),
        "cycle_defect_mean": float(np.mean(defects)) if defects else 0.0,
        "cycle_defect_rms": float(math.sqrt(np.mean(np.asarray(defects, dtype=np.float64) ** 2))) if defects else 0.0,
        "cycle_defect_max": float(max(defects, default=0.0)),
        "cycle_defect_density_mean": float(np.mean(defect_densities)) if defect_densities else 0.0,
        "cycle_defect_per_support_mean": float(np.mean(defect_per_supports)) if defect_per_supports else 0.0,
        "cycle_lower_bound_max": float(max(lower_bounds, default=0.0)),
        "mean_cycle_lower_bound": float(np.mean(lower_bounds)) if lower_bounds else 0.0,
        "cycle_lower_bound_sum": float(np.sum(lower_bounds)) if lower_bounds else 0.0,
        "cycle_lower_bound_normalized_max": float(max(lower_bound_normalized, default=0.0)),
        "cycle_lower_bound_normalized_mean": float(np.mean(lower_bound_normalized)) if lower_bound_normalized else 0.0,
        "cycle_lower_bound_normalized_sum": float(np.sum(lower_bound_normalized)) if lower_bound_normalized else 0.0,
        "cycle_lower_bound_surface_sum": float(np.sum(lower_bounds)) if lower_bounds else 0.0,
        "cycle_lower_bound_surface_density": float(_fraction(np.sum(lower_bounds), float(max(triad_count, 1)))),
        "cycle_lower_bound_support_weighted_sum": float(np.sum(lower_bound_support_weighted)) if lower_bound_support_weighted else 0.0,
        "cycle_projection_energy": float(projection_energy),
        "cycle_projection_energy_fraction": float(projection_energy_fraction),
        "cycle_independent_support_coverage": float(_fraction(float(np.count_nonzero(support_union)), float(triad_count))),
        "cycle_significant_count": float(sum(1 for value in lower_bounds if value > float(zero_eps))),
        "defective_cycle_count": float(defective_count),
        "cocycle_defect_mean": float(np.mean(defects)) if defects else 0.0,
        "cocycle_defect_max": float(max(defects, default=0.0)),
        "max_cycle_lower_bound": float(max(lower_bounds, default=0.0)),
        "triad_count": float(triad_count),
        "mode_count": float(mode_count),
    }


def _shell_row(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    shell_n: int,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "shell": int(shell_n),
        "top_k": int(top_k),
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
        amplitudes, phases, _, shell_coord = _mode_arrays(shell_modes)
        fitted_phase, _, _, _, phase_field_fit_rmse = _fit_phase_field(shell_modes, zero_eps=zero_eps)
        incidence, weights, closures, shell_spreads, distinct_shells = _build_incidence(shell_modes, triad_links)
        best_reference, best_shift, reference_rows = _choose_best_reference(
            phases=phases,
            amplitudes=amplitudes,
            shell_coord=shell_coord,
            fitted_phase=fitted_phase,
            triad_links=triad_links,
            zero_eps=zero_eps,
        )
        triad_count = len(triad_links)
        oracle_target, oracle_metrics = _triadwise_oracle_target(
            reference_rows=reference_rows,
            triad_count=triad_count,
        )
        adjusted_closures = np.asarray(
            [
                _wrap_phase(
                    float(phases[int(link.left)] - best_shift[int(link.left)])
                    + float(phases[int(link.right)] - best_shift[int(link.right)])
                    - float(phases[int(link.out)] - best_shift[int(link.out)])
                )
                for link in triad_links
            ],
            dtype=np.float64,
        )
        cycle_records, cycle_metrics = _cycle_lower_bounds(
            incidence=incidence,
            weights=np.asarray([float(link.weight) for link in triad_links], dtype=np.float64),
            target_cocycle=oracle_target,
            zero_eps=zero_eps,
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_cocycle_floor_scan_error: {exc}"]
        return ERROR_STATUS, row

    triad_count = len(triad_links)
    amp_sum = float(np.sum(amplitudes)) if len(amplitudes) else 0.0
    mode_concentration = _fraction(float(np.max(amplitudes)) if len(amplitudes) else 0.0, amp_sum)
    random_floor_proxy = float(np.mean(np.abs(closures))) if len(closures) else 0.0
    best_floor_proxy = float(best_reference["frustration_floor_proxy"])
    floor_ratio = _fraction(best_floor_proxy, max(random_floor_proxy, float(zero_eps)))

    row.update(
        {
            "selected_mode_count": int(len(shell_modes)),
            "selected_mode_amplitude_sum": float(amp_sum),
            "mode_concentration_fraction": float(mode_concentration),
            "triad_count": int(triad_count),
            "phase_field_fit_rmse": float(phase_field_fit_rmse),
            "best_reference_id": str(best_reference["reference_id"]),
            "best_reference_kind": str(best_reference["reference_kind"]),
            "best_reference_phase_slope": float(best_reference["phase_slope"]),
            "best_reference_phase_offset": float(best_reference["phase_offset"]),
            "best_reference_floor_proxy": float(best_floor_proxy),
            "best_reference_floor_rmse": float(best_reference["frustration_floor_rmse"]),
            "best_reference_lambda_max_proxy": float(best_reference["lambda_max_proxy"]),
            "best_reference_alignment_fraction": float(best_reference["triad_phase_alignment_fraction"]),
            "raw_closure_mean_abs": float(np.mean(np.abs(closures))) if len(closures) else 0.0,
            "adjusted_closure_mean_abs": float(np.mean(np.abs(adjusted_closures))) if len(adjusted_closures) else 0.0,
            "frustration_floor_ratio_vs_raw": float(floor_ratio),
            "oracle_reference_unique_count": int(oracle_metrics["oracle_reference_unique_count"]),
            "oracle_local_vs_global_disagreement_fraction": float(oracle_metrics["oracle_local_vs_global_disagreement_fraction"]),
            "oracle_reference_switch_fraction": float(oracle_metrics["oracle_reference_switch_fraction"]),
            "oracle_target_mean_abs": float(oracle_metrics["oracle_target_mean_abs"]),
            "oracle_target_rms": float(oracle_metrics["oracle_target_rms"]),
            "oracle_reference_head": list(oracle_metrics["oracle_reference_head"]),
            "shell_spread_mean": float(np.mean(shell_spreads)) if len(shell_spreads) else 0.0,
            "distinct_shell_count_mean": float(np.mean(distinct_shells)) if len(distinct_shells) else 0.0,
            "cycle_rank_proxy": float(cycle_metrics["cycle_rank"]),
            "independent_cycle_count": float(cycle_metrics["independent_cycle_count"]),
            "cycle_basis_dim": float(cycle_metrics["cycle_basis_dim"]),
            "cycle_basis_support_mean": float(cycle_metrics["cycle_basis_support_mean"]),
            "cycle_basis_support_max": float(cycle_metrics["cycle_basis_support_max"]),
            "cycle_basis_support_fraction_mean": float(cycle_metrics["cycle_basis_support_fraction_mean"]),
            "cycle_basis_weight_fraction_mean": float(cycle_metrics["cycle_basis_weight_fraction_mean"]),
            "cycle_basis_effective_support_mean": float(cycle_metrics["cycle_basis_effective_support_mean"]),
            "cycle_basis_dual_norm_mean": float(cycle_metrics["cycle_basis_dual_norm_mean"]),
            "cycle_basis_dual_norm_max": float(cycle_metrics["cycle_basis_dual_norm_max"]),
            "cycle_defect_mean": float(cycle_metrics["cycle_defect_mean"]),
            "cycle_defect_rms": float(cycle_metrics["cycle_defect_rms"]),
            "cycle_defect_max": float(cycle_metrics["cycle_defect_max"]),
            "cycle_defect_density_mean": float(cycle_metrics["cycle_defect_density_mean"]),
            "cycle_defect_per_support_mean": float(cycle_metrics["cycle_defect_per_support_mean"]),
            "defective_cycle_count": float(cycle_metrics["defective_cycle_count"]),
            "max_cycle_lower_bound": float(cycle_metrics["max_cycle_lower_bound"]),
            "mean_cycle_lower_bound": float(cycle_metrics["mean_cycle_lower_bound"]),
            "cycle_lower_bound_sum": float(cycle_metrics["cycle_lower_bound_sum"]),
            "cycle_lower_bound_normalized_max": float(cycle_metrics["cycle_lower_bound_normalized_max"]),
            "cycle_lower_bound_normalized_mean": float(cycle_metrics["cycle_lower_bound_normalized_mean"]),
            "cycle_lower_bound_normalized_sum": float(cycle_metrics["cycle_lower_bound_normalized_sum"]),
            "cycle_lower_bound_surface_sum": float(cycle_metrics["cycle_lower_bound_surface_sum"]),
            "cycle_lower_bound_surface_density": float(cycle_metrics["cycle_lower_bound_surface_density"]),
            "cycle_lower_bound_support_weighted_sum": float(cycle_metrics["cycle_lower_bound_support_weighted_sum"]),
            "cycle_projection_energy": float(cycle_metrics["cycle_projection_energy"]),
            "cycle_projection_energy_fraction": float(cycle_metrics["cycle_projection_energy_fraction"]),
            "cycle_independent_support_coverage": float(cycle_metrics["cycle_independent_support_coverage"]),
            "cycle_significant_count": float(cycle_metrics["cycle_significant_count"]),
            "cocycle_defect_mean": float(cycle_metrics["cocycle_defect_mean"]),
            "cocycle_defect_max": float(cycle_metrics["cocycle_defect_max"]),
            "cycle_records_head": cycle_records[: min(8, len(cycle_records))],
        }
    )

    warnings: list[str] = []
    if int(len(shell_modes)) < 3:
        warnings.append("shell carrier has fewer than three selected modes")
    if triad_count <= 0:
        warnings.append("no resonant triads in shell carrier")
    if float(cycle_metrics["cycle_rank"]) <= 0.0:
        warnings.append("cycle space collapsed for this shell carrier")
    if float(cycle_metrics["max_cycle_lower_bound"]) <= float(zero_eps):
        warnings.append("oracle cocycle lower bound collapsed to zero on this shell carrier")
    if warnings:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = warnings
        return PARTIAL_STATUS, row

    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]], shells: list[int]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            value = row.get(key)
            if isinstance(value, (int, float)) and math.isfinite(float(value)):
                values.append(float(value))
        return values

    return {
        "processed_rows": int(len(rows)),
        "ok_rows": int(sum(1 for row in rows if row.get("status") == OK_STATUS)),
        "partial_rows": int(sum(1 for row in rows if row.get("status") == PARTIAL_STATUS)),
        "error_rows": int(sum(1 for row in rows if row.get("status") == ERROR_STATUS)),
        "shells": [int(shell) for shell in shells],
        "top_k": int(ok_rows[0]["top_k"]) if ok_rows else None,
        "cycle_rank_proxy_mean": float(np.mean(_series("cycle_rank_proxy"))) if _series("cycle_rank_proxy") else None,
        "independent_cycle_count_mean": float(np.mean(_series("independent_cycle_count"))) if _series("independent_cycle_count") else None,
        "cycle_basis_dim_mean": float(np.mean(_series("cycle_basis_dim"))) if _series("cycle_basis_dim") else None,
        "cycle_basis_support_mean_mean": float(np.mean(_series("cycle_basis_support_mean"))) if _series("cycle_basis_support_mean") else None,
        "cycle_basis_support_max_mean": float(np.mean(_series("cycle_basis_support_max"))) if _series("cycle_basis_support_max") else None,
        "cycle_basis_weight_fraction_mean_mean": float(np.mean(_series("cycle_basis_weight_fraction_mean"))) if _series("cycle_basis_weight_fraction_mean") else None,
        "cycle_basis_effective_support_mean_mean": float(np.mean(_series("cycle_basis_effective_support_mean"))) if _series("cycle_basis_effective_support_mean") else None,
        "cycle_basis_dual_norm_max_mean": float(np.mean(_series("cycle_basis_dual_norm_max"))) if _series("cycle_basis_dual_norm_max") else None,
        "mean_cycle_lower_bound_mean": float(np.mean(_series("mean_cycle_lower_bound"))) if _series("mean_cycle_lower_bound") else None,
        "max_cycle_lower_bound_mean": float(np.mean(_series("max_cycle_lower_bound"))) if _series("max_cycle_lower_bound") else None,
        "cycle_lower_bound_normalized_mean_mean": float(np.mean(_series("cycle_lower_bound_normalized_mean")))
        if _series("cycle_lower_bound_normalized_mean")
        else None,
        "cycle_lower_bound_normalized_max_mean": float(np.mean(_series("cycle_lower_bound_normalized_max")))
        if _series("cycle_lower_bound_normalized_max")
        else None,
        "cycle_lower_bound_surface_sum_mean": float(np.mean(_series("cycle_lower_bound_surface_sum"))) if _series("cycle_lower_bound_surface_sum") else None,
        "cycle_lower_bound_surface_density_mean": float(np.mean(_series("cycle_lower_bound_surface_density"))) if _series("cycle_lower_bound_surface_density") else None,
        "cycle_lower_bound_support_weighted_sum_mean": float(np.mean(_series("cycle_lower_bound_support_weighted_sum"))) if _series("cycle_lower_bound_support_weighted_sum") else None,
        "cycle_projection_energy_mean": float(np.mean(_series("cycle_projection_energy"))) if _series("cycle_projection_energy") else None,
        "cycle_projection_energy_fraction_mean": float(np.mean(_series("cycle_projection_energy_fraction"))) if _series("cycle_projection_energy_fraction") else None,
        "cycle_independent_support_coverage_mean": float(np.mean(_series("cycle_independent_support_coverage"))) if _series("cycle_independent_support_coverage") else None,
        "cycle_significant_count_mean": float(np.mean(_series("cycle_significant_count"))) if _series("cycle_significant_count") else None,
        "frustration_floor_ratio_vs_raw_mean": float(np.mean(_series("frustration_floor_ratio_vs_raw")))
        if _series("frustration_floor_ratio_vs_raw")
        else None,
        "best_reference_lambda_max_proxy_mean": float(np.mean(_series("best_reference_lambda_max_proxy")))
        if _series("best_reference_lambda_max_proxy")
        else None,
        "oracle_reference_unique_count_mean": float(np.mean(_series("oracle_reference_unique_count")))
        if _series("oracle_reference_unique_count")
        else None,
        "oracle_local_vs_global_disagreement_fraction_mean": float(
            np.mean(_series("oracle_local_vs_global_disagreement_fraction"))
        )
        if _series("oracle_local_vs_global_disagreement_fraction")
        else None,
        "oracle_target_mean_abs_mean": float(np.mean(_series("oracle_target_mean_abs")))
        if _series("oracle_target_mean_abs")
        else None,
        "cocycle_defect_mean_mean": float(np.mean(_series("cocycle_defect_mean"))) if _series("cocycle_defect_mean") else None,
        "cycle_defect_mean_mean": float(np.mean(_series("cycle_defect_mean"))) if _series("cycle_defect_mean") else None,
        "cycle_defect_rms_mean": float(np.mean(_series("cycle_defect_rms"))) if _series("cycle_defect_rms") else None,
        "cycle_basis_dual_norm_mean_mean": float(np.mean(_series("cycle_basis_dual_norm_mean"))) if _series("cycle_basis_dual_norm_mean") else None,
        "cycle_basis_support_fraction_mean_mean": float(np.mean(_series("cycle_basis_support_fraction_mean"))) if _series("cycle_basis_support_fraction_mean") else None,
        "cycle_rank_vs_floor_ratio_correlation": _pearson(
            _series("cycle_rank_proxy"),
            _series("frustration_floor_ratio_vs_raw"),
        ),
        "cycle_lower_bound_vs_projection_energy_correlation": _pearson(
            _series("cycle_lower_bound_sum"),
            _series("cycle_projection_energy"),
        ),
        "cycle_lower_bound_normalized_vs_defect_correlation": _pearson(
            _series("cycle_lower_bound_normalized_sum"),
            _series("cycle_defect_mean"),
        ),
        "cycle_lower_bound_vs_defect_correlation": _pearson(
            _series("cycle_lower_bound_sum"),
            _series("cycle_defect_mean"),
        ),
        "cycle_lower_bound_vs_oracle_disagreement_correlation": _pearson(
            _series("cycle_lower_bound_sum"),
            _series("oracle_local_vs_global_disagreement_fraction"),
        ),
        "cycle_basis_dim_vs_floor_ratio_correlation": _pearson(
            _series("cycle_basis_dim"),
            _series("frustration_floor_ratio_vs_raw"),
        ),
        "cycle_projection_energy_fraction_vs_floor_ratio_correlation": _pearson(
            _series("cycle_projection_energy_fraction"),
            _series("frustration_floor_ratio_vs_raw"),
        ),
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells)
    warnings: list[str] = []
    try:
        bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
        frame_indices = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)
    except Exception as exc:  # noqa: BLE001
        payload = {
            "contract": CONTRACT,
            "schema_version": SCHEMA_VERSION,
            "route_decision": ROUTE_DECISION,
            "script_name": SCRIPT_NAME,
            "control_card": CONTROL_CARD,
            "authority": AUTHORITY,
            "parameters": {
                "raw_archive": str(args.raw_archive),
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "top_k": int(args.top_k),
                "pool_multiplier": int(args.pool_multiplier),
                "zero_eps": float(args.zero_eps),
                "shells": [int(shell) for shell in shells],
                "seed": int(args.seed),
            },
            "rows": [],
            "aggregate": _aggregate_rows([], shells),
            "warnings": warnings,
            "errors": [str(exc)],
            "status": ERROR_STATUS,
            "route_mode": "fail-closed",
            "fail_closed": True,
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty)
        args.output_json.write_text(text + "\n", encoding="utf-8")
        print(text)
        return 1
    if not frame_indices:
        payload = {
            "contract": CONTRACT,
            "schema_version": SCHEMA_VERSION,
            "route_decision": ROUTE_DECISION,
            "script_name": SCRIPT_NAME,
            "control_card": CONTROL_CARD,
            "authority": AUTHORITY,
            "parameters": {
                "raw_archive": str(args.raw_archive),
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "top_k": int(args.top_k),
                "pool_multiplier": int(args.pool_multiplier),
                "zero_eps": float(args.zero_eps),
                "shells": [int(shell) for shell in shells],
                "seed": int(args.seed),
            },
            "rows": [],
            "aggregate": _aggregate_rows([], shells),
            "warnings": warnings,
            "errors": ["no frames selected for cocycle floor scan"],
            "status": ERROR_STATUS,
            "route_mode": "fail-closed",
            "fail_closed": True,
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty)
        args.output_json.write_text(text + "\n", encoding="utf-8")
        print(text)
        return 1

    rows: list[dict[str, Any]] = []
    for slot, snapshot in enumerate(frame_indices):
        for shell_n in shells:
            status, row = _shell_row(
                slot=slot,
                snapshot=int(snapshot),
                bundle=bundle,
                top_k=int(args.top_k),
                pool_multiplier=int(args.pool_multiplier),
                zero_eps=float(args.zero_eps),
                shell_n=int(shell_n),
            )
            row["status"] = status
            rows.append(row)

    payload = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "authority": AUTHORITY,
        "parameters": {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "shells": [int(shell) for shell in shells],
            "seed": int(args.seed),
        },
        "rows": rows,
        "aggregate": _aggregate_rows(rows, shells),
        "warnings": warnings,
        "errors": [],
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
