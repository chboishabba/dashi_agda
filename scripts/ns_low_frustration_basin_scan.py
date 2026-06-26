#!/usr/bin/env python3
"""Empirically scan low-frustration basin occupancy around the best triad reference.

The scan is candidate-only and fail-closed. It reuses the existing selected-mode
carrier, triad construction, and fitted phase-field machinery, then probes a
small reference family and samples perturbations around the best empirical
reference. The result is telemetry only: basin occupancy, rarity proxies, and
structured-vs-random perturbation comparisons, not a theorem or promotion.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_orbit_phase_coherence_scan import (  # type: ignore
    ModeRecord,
    _collect_modes,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_triad_frustration_defect_scan import _fit_phase_field  # type: ignore


SCRIPT_NAME = "scripts/ns_low_frustration_basin_scan.py"
CONTRACT = "ns_low_frustration_basin_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_LOW_FRUSTRATION_BASIN_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_low_frustration_basin_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_DELTA_BANDS = (0.05, 0.10, 0.20, 0.35)
DEFAULT_RANDOM_SAMPLES = 128
DEFAULT_STRUCTURED_GRID = 5
DEFAULT_SEED = 0
DEFAULT_STRUCTURED_SLOPES = (-1.0, -0.5, 0.5, 1.0)
NEGATIVE_LOG_VOLUME_EPS = 1.0e-12

CONTROL_CARD = {
    "O": "Empirically scan low-frustration basin occupancy around the best triad reference.",
    "R": (
        "Rebuild the selected-mode triad carrier, choose the best empirical reference, "
        "and probe how thin the low-frustration basin looks under perturbations."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; basin occupancy and rarity proxies are empirical only.",
    "L": (
        "Load raw frames, reuse the selected Fourier-vorticity triad machinery, "
        "choose the best reference, and sample random plus structured perturbations around it."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, residence-time exclusion, or promotion claim is inferred.",
    "F": "This scan estimates basin rarity only; it does not prove exclusion or closure."
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


@dataclass(frozen=True)
class ReferenceSpec:
    reference_id: str
    reference_kind: str
    phase_slope: float
    weight_power: float
    uses_shell_geometry: bool
    uses_fitted_field: bool = False


@dataclass(frozen=True)
class TriadLink:
    left: int
    right: int
    out: int
    weight: float
    shell_spread: float


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
        "--delta-band",
        dest="delta_bands",
        action="append",
        type=float,
        default=None,
        help="Absolute phase perturbation band in radians; may be repeated.",
    )
    parser.add_argument("--random-samples", type=int, default=DEFAULT_RANDOM_SAMPLES)
    parser.add_argument("--structured-grid", type=int, default=DEFAULT_STRUCTURED_GRID)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _wrap_phase_array(values: np.ndarray | float) -> np.ndarray | float:
    return np.arctan2(np.sin(values), np.cos(values))


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _fraction(numerator: float, denominator: float) -> float:
    if denominator <= 0.0:
        return 0.0
    return float(numerator) / float(denominator)


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


def _weighted_circular_mean(phases: np.ndarray, weights: np.ndarray) -> float:
    total = float(np.sum(weights))
    if total <= 0.0:
        return 0.0
    z = np.sum(np.asarray(weights, dtype=np.float64) * np.exp(1j * np.asarray(phases, dtype=np.float64)))
    if abs(z) <= 0.0:
        return 0.0
    return float(math.atan2(z.imag, z.real))


def _mode_arrays(modes: list[ModeRecord]) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
    phases = np.asarray([mode.phase for mode in modes], dtype=np.float64)
    shell_radii = np.asarray([mode.shell_radius for mode in modes], dtype=np.float64)
    shell_center = float(np.mean(shell_radii)) if len(shell_radii) else 0.0
    shell_span = float(np.max(shell_radii) - np.min(shell_radii)) if len(shell_radii) else 0.0
    shell_scale = shell_span if shell_span > 0.0 else 1.0
    shell_coord = (shell_radii - shell_center) / shell_scale
    return amplitudes, phases, shell_radii, shell_coord


def _reference_specs() -> list[ReferenceSpec]:
    specs = [
        ReferenceSpec("zero", "global", 0.0, 1.0, False),
        ReferenceSpec("global_resultant", "global", 0.0, 1.0, False),
        ReferenceSpec("global_energy_resultant", "global", 0.0, 2.0, False),
        ReferenceSpec("dominant_mode_anchor", "global", 0.0, 1.0, False),
        ReferenceSpec("fitted_phase_field", "fitted", 0.0, 1.0, False, True),
    ]
    for slope in DEFAULT_STRUCTURED_SLOPES:
        specs.append(
            ReferenceSpec(
                reference_id=f"shell_affine_{slope:+.2f}",
                reference_kind="structured",
                phase_slope=float(slope),
                weight_power=1.0,
                uses_shell_geometry=True,
            )
        )
    return specs


def _reference_shift(
    spec: ReferenceSpec,
    phases: np.ndarray,
    amplitudes: np.ndarray,
    shell_coord: np.ndarray,
    fitted_phase: np.ndarray,
) -> tuple[float, np.ndarray]:
    if spec.reference_id == "zero":
        shift = np.zeros_like(phases, dtype=np.float64)
        return 0.0, shift
    if spec.reference_id == "dominant_mode_anchor":
        offset = float(phases[int(np.argmax(amplitudes))]) if len(phases) else 0.0
        return offset, np.full_like(phases, offset, dtype=np.float64)
    if spec.reference_id == "fitted_phase_field":
        shift = np.asarray(fitted_phase, dtype=np.float64)
        offset = _weighted_circular_mean(shift, amplitudes) if len(shift) else 0.0
        return offset, shift

    slope = float(spec.phase_slope)
    base_phases = phases - (slope * shell_coord) if spec.uses_shell_geometry else phases
    weights = np.power(np.asarray(amplitudes, dtype=np.float64), float(spec.weight_power))
    offset = _weighted_circular_mean(base_phases, weights)
    shift = offset + (slope * shell_coord)
    return offset, np.asarray(shift, dtype=np.float64)


def _build_triad_links(modes: list[ModeRecord], zero_eps: float) -> list[TriadLink]:
    if len(modes) < 3:
        return []
    key_to_index = {mode.key: index for index, mode in enumerate(modes)}
    links: list[TriadLink] = []
    for left in range(len(modes)):
        mode_left = modes[left]
        for right in range(left, len(modes)):
            mode_right = modes[right]
            key_out = (
                mode_left.key[0] + mode_right.key[0],
                mode_left.key[1] + mode_right.key[1],
                mode_left.key[2] + mode_right.key[2],
            )
            out = key_to_index.get(key_out)
            if out is None or out == left or out == right:
                continue
            mode_out = modes[out]
            weight = mode_left.amplitude * mode_right.amplitude * mode_out.amplitude
            if not math.isfinite(weight) or weight <= float(zero_eps):
                continue
            shell_spread = max(mode_left.shell_radius, mode_right.shell_radius, mode_out.shell_radius) - min(
                mode_left.shell_radius,
                mode_right.shell_radius,
                mode_out.shell_radius,
            )
            links.append(
                TriadLink(
                    left=int(left),
                    right=int(right),
                    out=int(out),
                    weight=float(weight),
                    shell_spread=float(shell_spread),
                )
            )
    return links


def _score_shift_batch(
    phases: np.ndarray,
    shifts: np.ndarray,
    left_idx: np.ndarray,
    right_idx: np.ndarray,
    out_idx: np.ndarray,
    weights: np.ndarray,
    zero_eps: float,
) -> dict[str, np.ndarray]:
    shifts = np.asarray(shifts, dtype=np.float64)
    if shifts.ndim == 0:
        shifts = np.full((1, len(phases)), float(shifts), dtype=np.float64)
    elif shifts.ndim == 1:
        shifts = shifts[None, :]
    if shifts.size == 0:
        empty = np.zeros(0, dtype=np.float64)
        return {
            "score_mean_abs": empty,
            "score_rmse": empty,
            "score_coherence": empty,
            "score_alignment_fraction": empty,
            "residual_abs": np.zeros((0, len(weights)), dtype=np.float64),
        }

    adjusted = np.asarray(_wrap_phase_array(phases[None, :] - shifts), dtype=np.float64)
    residuals = np.asarray(
        _wrap_phase_array(
            adjusted[:, left_idx] + adjusted[:, right_idx] - adjusted[:, out_idx]
        ),
        dtype=np.float64,
    )
    abs_residuals = np.abs(residuals)
    total_weight = float(np.sum(weights))
    if total_weight <= 0.0 or not math.isfinite(total_weight):
        total_weight = 1.0
    weighted_abs = np.sum(abs_residuals * weights[None, :], axis=1) / total_weight
    weighted_rmse = np.sqrt(np.sum((residuals * residuals) * weights[None, :], axis=1) / total_weight)
    weighted_complex = np.sum(np.exp(1j * residuals) * weights[None, :], axis=1)
    coherence = np.abs(weighted_complex) / total_weight
    alignment = np.sum((abs_residuals <= float(zero_eps)) * weights[None, :], axis=1) / total_weight
    return {
        "score_mean_abs": np.asarray(weighted_abs, dtype=np.float64),
        "score_rmse": np.asarray(weighted_rmse, dtype=np.float64),
        "score_coherence": np.asarray(coherence, dtype=np.float64),
        "score_alignment_fraction": np.asarray(alignment, dtype=np.float64),
        "residual_abs": np.asarray(abs_residuals, dtype=np.float64),
    }


def _candidate_rows(
    modes: list[ModeRecord],
    triad_links: list[TriadLink],
    zero_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    amplitudes, phases, _, shell_coord = _mode_arrays(modes)
    fitted_phase, _, _, _, phase_field_fit_rmse = _fit_phase_field(modes, zero_eps=zero_eps)

    if not triad_links:
        empty: dict[str, Any] = {}
        return [], empty, empty, empty, {
            "phase_field_fit_rmse": float(phase_field_fit_rmse),
            "fitted_phase": np.asarray(fitted_phase, dtype=np.float64),
            "shell_coord": np.asarray(shell_coord, dtype=np.float64),
            "amplitudes": np.asarray(amplitudes, dtype=np.float64),
            "phases": np.asarray(phases, dtype=np.float64),
        }

    left_idx = np.asarray([link.left for link in triad_links], dtype=np.int64)
    right_idx = np.asarray([link.right for link in triad_links], dtype=np.int64)
    out_idx = np.asarray([link.out for link in triad_links], dtype=np.int64)
    weights = np.asarray([link.weight for link in triad_links], dtype=np.float64)
    triad_shell_spread = np.asarray([link.shell_spread for link in triad_links], dtype=np.float64)
    total_weight = float(np.sum(weights))
    if total_weight <= 0.0 or not math.isfinite(total_weight):
        total_weight = 1.0

    candidate_rows: list[dict[str, Any]] = []
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
        abs_residual = np.asarray(scores["residual_abs"][0], dtype=np.float64)
        floor_proxy = float(np.sum(weights * abs_residual) / total_weight)
        floor_rmse = float(scores["score_rmse"][0])
        floor_p95 = float(_weighted_quantile(abs_residual, weights, 0.95))
        phase_coherence = float(scores["score_coherence"][0])
        alignment_fraction = float(scores["score_alignment_fraction"][0])
        shift_rms = float(math.sqrt(float(np.mean(np.square(np.asarray(_wrap_phase_array(shift), dtype=np.float64)))))) if len(shift) else 0.0
        candidate_rows.append(
            {
                "reference_id": spec.reference_id,
                "reference_kind": spec.reference_kind,
                "phase_slope": float(spec.phase_slope),
                "phase_offset": float(_wrap_phase_array(offset)),
                "phase_shift_rms": shift_rms,
                "frustration_floor_proxy": floor_proxy,
                "frustration_floor_rmse": floor_rmse,
                "frustration_floor_p95": floor_p95,
                "triad_phase_coherence": phase_coherence,
                "phase_alignment_fraction": alignment_fraction,
                "triad_count": int(len(triad_links)),
            }
        )

    candidate_rows.sort(
        key=lambda row: (
            float(row["frustration_floor_proxy"]),
            float(row["frustration_floor_rmse"]),
            -float(row["triad_phase_coherence"]),
            float(row["phase_shift_rms"]),
        )
    )
    for rank, row in enumerate(candidate_rows, start=1):
        row["reference_rank"] = int(rank)

    by_id = {row["reference_id"]: row for row in candidate_rows}
    zero_row = by_id["zero"]
    global_rows = [row for row in candidate_rows if row["reference_kind"] == "global"]
    structured_rows = [row for row in candidate_rows if row["reference_kind"] == "structured"]
    best_global = global_rows[0] if global_rows else {}
    best_structured = structured_rows[0] if structured_rows else {}
    return (
        candidate_rows,
        zero_row,
        best_global,
        best_structured,
        {
            "phase_field_fit_rmse": float(phase_field_fit_rmse),
            "fitted_phase": np.asarray(fitted_phase, dtype=np.float64),
            "shell_coord": np.asarray(shell_coord, dtype=np.float64),
            "amplitudes": np.asarray(amplitudes, dtype=np.float64),
            "phases": np.asarray(phases, dtype=np.float64),
            "weights": weights,
            "left_idx": left_idx,
            "right_idx": right_idx,
            "out_idx": out_idx,
            "triad_shell_spread": triad_shell_spread,
            "total_weight": float(total_weight),
        },
    )


def _structured_shifts(center_shift: np.ndarray, shell_coord: np.ndarray, delta_band: float, grid: int) -> np.ndarray:
    grid = max(1, int(grid))
    coeffs = np.linspace(-float(delta_band), float(delta_band), num=grid, dtype=np.float64)
    samples = [center_shift + offset + slope * shell_coord for offset in coeffs for slope in coeffs]
    return np.asarray(samples, dtype=np.float64)


def _random_shifts(center_shift: np.ndarray, delta_band: float, samples: int, seed: int) -> np.ndarray:
    if samples <= 0:
        return np.zeros((0, len(center_shift)), dtype=np.float64)
    rng = np.random.default_rng(seed)
    noise = rng.normal(loc=0.0, scale=float(delta_band), size=(int(samples), len(center_shift)))
    return np.asarray(center_shift[None, :] + noise, dtype=np.float64)


def _delta_band_row(
    delta_band: float,
    center_shift: np.ndarray,
    shell_coord: np.ndarray,
    phases: np.ndarray,
    left_idx: np.ndarray,
    right_idx: np.ndarray,
    out_idx: np.ndarray,
    weights: np.ndarray,
    best_floor_proxy: float,
    structured_grid: int,
    random_samples: int,
    seed: int,
) -> dict[str, Any]:
    structured_shifts = _structured_shifts(center_shift, shell_coord, delta_band=delta_band, grid=structured_grid)
    random_shifts = _random_shifts(center_shift, delta_band=delta_band, samples=random_samples, seed=seed)
    threshold = float(best_floor_proxy + float(delta_band))

    structured_scores = _score_shift_batch(
        phases=phases,
        shifts=structured_shifts,
        left_idx=left_idx,
        right_idx=right_idx,
        out_idx=out_idx,
        weights=weights,
        zero_eps=NEGATIVE_LOG_VOLUME_EPS,
    )
    random_scores = _score_shift_batch(
        phases=phases,
        shifts=random_shifts,
        left_idx=left_idx,
        right_idx=right_idx,
        out_idx=out_idx,
        weights=weights,
        zero_eps=NEGATIVE_LOG_VOLUME_EPS,
    )

    structured_mean = np.asarray(structured_scores["score_mean_abs"], dtype=np.float64)
    random_mean = np.asarray(random_scores["score_mean_abs"], dtype=np.float64)
    structured_occupancy = _fraction(float(np.count_nonzero(structured_mean <= threshold)), float(len(structured_mean)))
    random_occupancy = _fraction(float(np.count_nonzero(random_mean <= threshold)), float(len(random_mean)))
    combined_total = float(len(structured_mean) + len(random_mean))
    combined_hits = float(np.count_nonzero(structured_mean <= threshold) + np.count_nonzero(random_mean <= threshold))
    occupancy = _fraction(combined_hits, combined_total)
    rarity_proxy = float(-math.log(max(occupancy, NEGATIVE_LOG_VOLUME_EPS)))
    structured_mean_score = float(np.mean(structured_mean)) if len(structured_mean) else 0.0
    random_mean_score = float(np.mean(random_mean)) if len(random_mean) else 0.0
    structured_p95 = float(np.quantile(structured_mean, 0.95)) if len(structured_mean) else 0.0
    random_p95 = float(np.quantile(random_mean, 0.95)) if len(random_mean) else 0.0
    combined_p95 = float(
        np.quantile(np.concatenate([structured_mean, random_mean]), 0.95)
    ) if combined_total > 0.0 else 0.0
    structured_thinness = float(1.0 - structured_occupancy)
    random_thinness = float(1.0 - random_occupancy)
    return {
        "delta_band": float(delta_band),
        "threshold": float(threshold),
        "structured_sample_count": int(len(structured_mean)),
        "random_sample_count": int(len(random_mean)),
        "sample_count": int(combined_total),
        "occupancy_fraction": float(occupancy),
        "structured_occupancy_fraction": float(structured_occupancy),
        "random_occupancy_fraction": float(random_occupancy),
        "negative_log_volume_proxy": float(rarity_proxy),
        "structured_minus_random_occupancy_gap": float(structured_occupancy - random_occupancy),
        "structured_minus_random_floor_gap": float(structured_mean_score - random_mean_score),
        "structured_thinness_proxy": float(structured_thinness),
        "random_thinness_proxy": float(random_thinness),
        "structured_mean_floor_proxy": float(structured_mean_score),
        "random_mean_floor_proxy": float(random_mean_score),
        "combined_mean_floor_proxy": float(
            (
                (structured_mean_score * len(structured_mean))
                + (random_mean_score * len(random_mean))
            )
            / combined_total
        ),
        "structured_floor_p95": float(structured_p95),
        "random_floor_p95": float(random_p95),
        "combined_floor_p95": float(combined_p95),
        "structured_min_floor_proxy": float(np.min(structured_mean)) if len(structured_mean) else 0.0,
        "random_min_floor_proxy": float(np.min(random_mean)) if len(random_mean) else 0.0,
        "threshold_gap": float(delta_band),
        "structured_samples": {
            "family": "grid_shell_affine",
            "grid_size": int(structured_grid),
        },
        "random_samples": {
            "family": "gaussian_full_space",
            "seed": int(seed),
        },
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    delta_bands: list[float],
    random_samples: int,
    structured_grid: int,
    seed: int,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "orbit_phase": float(snapshot),
        "source": str(bundle.path),
        "top_k": int(top_k),
        "pool_multiplier": int(pool_multiplier),
        "zero_eps": float(zero_eps),
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "reference_family": "best_reference_centered_basin_scan",
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
        triad_links = _build_triad_links(modes, zero_eps=zero_eps)
        candidate_rows, zero_row, best_global, best_structured, derived = _candidate_rows(
            modes=modes,
            triad_links=triad_links,
            zero_eps=zero_eps,
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_low_frustration_basin_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(len(modes)),
            "selected_mode_amplitude_sum": float(sum(mode.amplitude for mode in modes)),
            "triad_count": int(len(triad_links)),
            "phase_field_fit_rmse": float(derived["phase_field_fit_rmse"]),
            "reference_candidate_count": int(len(candidate_rows)),
            "reference_candidates": candidate_rows,
            "zero_reference_floor_proxy": float(zero_row["frustration_floor_proxy"]) if zero_row else None,
            "zero_reference_floor_rmse": float(zero_row["frustration_floor_rmse"]) if zero_row else None,
            "best_global_reference_id": best_global.get("reference_id") if best_global else None,
            "best_global_reference_rank": int(best_global["reference_rank"]) if best_global else None,
            "best_global_floor_proxy": float(best_global["frustration_floor_proxy"]) if best_global else None,
            "best_structured_reference_id": best_structured.get("reference_id") if best_structured else None,
            "best_structured_reference_rank": int(best_structured["reference_rank"]) if best_structured else None,
            "best_structured_floor_proxy": float(best_structured["frustration_floor_proxy"]) if best_structured else None,
        }
    )

    if not candidate_rows or not triad_links:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no resonant selected-mode triads found for basin scan"]
        row["delta_band_rows"] = []
        row["best_reference_id"] = None
        row["best_reference_kind"] = None
        row["best_reference_rank"] = None
        row["best_reference_phase_slope"] = None
        row["best_reference_phase_offset"] = None
        row["best_reference_phase_shift_rms"] = None
        row["best_reference_floor_proxy"] = None
        row["best_reference_floor_rmse"] = None
        row["best_reference_floor_p95"] = None
        row["best_reference_phase_coherence"] = None
        row["best_reference_phase_alignment_fraction"] = None
        row["best_reference_is_zero"] = False
        row["best_reference_is_structured"] = False
        row["best_reference_is_fitted"] = False
        row["best_reference_floor_improvement_over_zero"] = None
        row["best_reference_floor_improvement_over_best_global"] = None
        row["best_structured_floor_improvement_over_best_global"] = None
        row["basin_occupancy_mean"] = None
        row["negative_log_volume_proxy_mean"] = None
        return PARTIAL_STATUS, row

    winner = candidate_rows[0]
    center_shift = np.asarray(
        _reference_shift(
            spec=ReferenceSpec(
                reference_id=winner["reference_id"],
                reference_kind=winner["reference_kind"],
                phase_slope=float(winner["phase_slope"]),
                weight_power=1.0,
                uses_shell_geometry=winner["reference_kind"] == "structured",
                uses_fitted_field=winner["reference_kind"] == "fitted",
            ),
            phases=np.asarray(derived["phases"], dtype=np.float64),
            amplitudes=np.asarray(derived["amplitudes"], dtype=np.float64),
            shell_coord=np.asarray(derived["shell_coord"], dtype=np.float64),
            fitted_phase=np.asarray(derived["fitted_phase"], dtype=np.float64),
        )[1],
        dtype=np.float64,
    )

    left_idx = np.asarray(derived["left_idx"], dtype=np.int64)
    right_idx = np.asarray(derived["right_idx"], dtype=np.int64)
    out_idx = np.asarray(derived["out_idx"], dtype=np.int64)
    weights = np.asarray(derived["weights"], dtype=np.float64)
    phases = np.asarray(derived["phases"], dtype=np.float64)
    shell_coord = np.asarray(derived["shell_coord"], dtype=np.float64)

    delta_rows: list[dict[str, Any]] = []
    for delta_index, delta_band in enumerate(delta_bands):
        delta_rows.append(
            _delta_band_row(
                delta_band=float(delta_band),
                center_shift=center_shift,
                shell_coord=shell_coord,
                phases=phases,
                left_idx=left_idx,
                right_idx=right_idx,
                out_idx=out_idx,
                weights=weights,
                best_floor_proxy=float(winner["frustration_floor_proxy"]),
                structured_grid=int(structured_grid),
                random_samples=int(random_samples),
                seed=int(seed + slot * 10007 + delta_index * 1009),
            )
        )

    row.update(
        {
            "status": OK_STATUS,
            "best_reference_id": winner["reference_id"],
            "best_reference_kind": winner["reference_kind"],
            "best_reference_rank": int(winner["reference_rank"]),
            "best_reference_phase_slope": float(winner["phase_slope"]),
            "best_reference_phase_offset": float(winner["phase_offset"]),
            "best_reference_phase_shift_rms": float(winner["phase_shift_rms"]),
            "best_reference_floor_proxy": float(winner["frustration_floor_proxy"]),
            "best_reference_floor_rmse": float(winner["frustration_floor_rmse"]),
            "best_reference_floor_p95": float(winner["frustration_floor_p95"]),
            "best_reference_phase_coherence": float(winner["triad_phase_coherence"]),
            "best_reference_phase_alignment_fraction": float(winner["phase_alignment_fraction"]),
            "best_reference_is_zero": bool(winner["reference_id"] == "zero"),
            "best_reference_is_structured": bool(winner["reference_kind"] == "structured"),
            "best_reference_is_fitted": bool(winner["reference_kind"] == "fitted"),
            "best_reference_floor_improvement_over_zero": (
                float(zero_row["frustration_floor_proxy"] - winner["frustration_floor_proxy"])
                if zero_row
                else None
            ),
            "best_reference_floor_improvement_over_best_global": (
                float(best_global["frustration_floor_proxy"] - winner["frustration_floor_proxy"])
                if best_global
                else None
            ),
            "best_structured_floor_improvement_over_best_global": (
                float(best_global["frustration_floor_proxy"] - best_structured["frustration_floor_proxy"])
                if best_structured and best_global
                else None
            ),
            "delta_band_rows": delta_rows,
            "basin_occupancy_mean": float(np.mean([row["occupancy_fraction"] for row in delta_rows])) if delta_rows else 0.0,
            "negative_log_volume_proxy_mean": float(np.mean([row["negative_log_volume_proxy"] for row in delta_rows])) if delta_rows else 0.0,
        }
    )
    return OK_STATUS, row


def _aggregate_rows(
    rows: list[dict[str, Any]],
    delta_bands: list[float],
) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    partial_rows = [row for row in rows if row.get("status") == PARTIAL_STATUS]
    error_rows = [row for row in rows if row.get("status") == ERROR_STATUS]

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            parsed = _finite_float(row.get(key))
            if parsed is not None:
                values.append(parsed)
        return values

    delta_band_aggregates: list[dict[str, Any]] = []
    for band_index, delta_band in enumerate(delta_bands):
        band_rows = [
            row["delta_band_rows"][band_index]
            for row in ok_rows
            if isinstance(row.get("delta_band_rows"), list) and len(row["delta_band_rows"]) > band_index
        ]
        if not band_rows:
            delta_band_aggregates.append(
                {
                    "delta_band": float(delta_band),
                    "frame_count": 0,
                    "occupancy_fraction_mean": None,
                    "structured_occupancy_fraction_mean": None,
                    "random_occupancy_fraction_mean": None,
                    "negative_log_volume_proxy_mean": None,
                    "structured_minus_random_occupancy_gap_mean": None,
                    "structured_minus_random_floor_gap_mean": None,
                    "structured_mean_floor_proxy_mean": None,
                    "random_mean_floor_proxy_mean": None,
                }
            )
            continue
        delta_band_aggregates.append(
            {
                "delta_band": float(delta_band),
                "frame_count": int(len(band_rows)),
                "occupancy_fraction_mean": float(np.mean([row["occupancy_fraction"] for row in band_rows])),
                "structured_occupancy_fraction_mean": float(np.mean([row["structured_occupancy_fraction"] for row in band_rows])),
                "random_occupancy_fraction_mean": float(np.mean([row["random_occupancy_fraction"] for row in band_rows])),
                "negative_log_volume_proxy_mean": float(np.mean([row["negative_log_volume_proxy"] for row in band_rows])),
                "structured_minus_random_occupancy_gap_mean": float(
                    np.mean([row["structured_minus_random_occupancy_gap"] for row in band_rows])
                ),
                "structured_minus_random_floor_gap_mean": float(
                    np.mean([row["structured_minus_random_floor_gap"] for row in band_rows])
                ),
                "structured_mean_floor_proxy_mean": float(np.mean([row["structured_mean_floor_proxy"] for row in band_rows])),
                "random_mean_floor_proxy_mean": float(np.mean([row["random_mean_floor_proxy"] for row in band_rows])),
            }
        )

    best_floor = _series("best_reference_floor_proxy")
    zero_floor = _series("zero_reference_floor_proxy")
    basin_occupancy = _series("basin_occupancy_mean")
    rarity = _series("negative_log_volume_proxy_mean")
    selected_mode_count = _series("selected_mode_count")
    triad_count = _series("triad_count")
    phase_field_fit_rmse = _series("phase_field_fit_rmse")
    best_improvement_over_zero = _series("best_reference_floor_improvement_over_zero")
    best_improvement_over_global = _series("best_reference_floor_improvement_over_best_global")
    structured_gap = _series("best_structured_floor_improvement_over_best_global")

    return {
        "processed_frames": len(rows),
        "ok_frames": len(ok_rows),
        "partial_frames": len(partial_rows),
        "error_frames": len(error_rows),
        "reference_family": "best_reference_centered_basin_scan",
        "top_k": int(ok_rows[0]["top_k"]) if ok_rows else None,
        "pool_multiplier": int(ok_rows[0]["pool_multiplier"]) if ok_rows else None,
        "zero_eps": float(ok_rows[0]["zero_eps"]) if ok_rows else None,
        "random_samples": int(ok_rows[0]["delta_band_rows"][0]["random_sample_count"]) if ok_rows and ok_rows[0].get("delta_band_rows") else None,
        "structured_grid": int(ok_rows[0]["delta_band_rows"][0]["structured_samples"]["grid_size"]) if ok_rows and ok_rows[0].get("delta_band_rows") else None,
        "delta_band_rows": delta_band_aggregates,
        "selected_mode_count_mean": float(np.mean(selected_mode_count)) if selected_mode_count else None,
        "triad_count_mean": float(np.mean(triad_count)) if triad_count else None,
        "phase_field_fit_rmse_mean": float(np.mean(phase_field_fit_rmse)) if phase_field_fit_rmse else None,
        "best_reference_floor_proxy_mean": float(np.mean(best_floor)) if best_floor else None,
        "zero_reference_floor_proxy_mean": float(np.mean(zero_floor)) if zero_floor else None,
        "best_reference_floor_improvement_over_zero_mean": float(np.mean(best_improvement_over_zero)) if best_improvement_over_zero else None,
        "best_reference_floor_improvement_over_best_global_mean": float(np.mean(best_improvement_over_global)) if best_improvement_over_global else None,
        "best_structured_floor_improvement_over_best_global_mean": float(np.mean(structured_gap)) if structured_gap else None,
        "basin_occupancy_mean": float(np.mean(basin_occupancy)) if basin_occupancy else None,
        "negative_log_volume_proxy_mean": float(np.mean(rarity)) if rarity else None,
        "basin_occupancy_median": float(np.median(basin_occupancy)) if basin_occupancy else None,
        "negative_log_volume_proxy_median": float(np.median(rarity)) if rarity else None,
        "best_reference_is_zero_fraction": _fraction(
            float(sum(1 for row in ok_rows if row.get("best_reference_is_zero") is True)),
            float(len(ok_rows)),
        ) if ok_rows else None,
        "best_reference_is_structured_fraction": _fraction(
            float(sum(1 for row in ok_rows if row.get("best_reference_is_structured") is True)),
            float(len(ok_rows)),
        ) if ok_rows else None,
        "best_reference_is_fitted_fraction": _fraction(
            float(sum(1 for row in ok_rows if row.get("best_reference_is_fitted") is True)),
            float(len(ok_rows)),
        ) if ok_rows else None,
        "occupancy_vs_best_floor_correlation": _pearson(best_floor, basin_occupancy),
        "rarity_vs_best_floor_correlation": _pearson(best_floor, rarity),
        "triad_count_vs_basin_occupancy_correlation": _pearson(triad_count, basin_occupancy),
        "best_floor_vs_zero_floor_correlation": _pearson(best_floor, zero_floor),
    }


def _validate_parameters(args: argparse.Namespace) -> list[float]:
    delta_bands = list(DEFAULT_DELTA_BANDS if args.delta_bands is None else args.delta_bands)
    if not delta_bands:
        raise SystemExit("--delta-band must be provided at least once or left at the default band set")
    for band in delta_bands:
        if not math.isfinite(float(band)) or float(band) <= 0.0:
            raise SystemExit("--delta-band values must be finite and positive")
    if int(args.random_samples) <= 0:
        raise SystemExit("--random-samples must be positive")
    if int(args.structured_grid) <= 0:
        raise SystemExit("--structured-grid must be positive")
    if int(args.top_k) <= 0:
        raise SystemExit("--top-k must be positive")
    if int(args.pool_multiplier) <= 0:
        raise SystemExit("--pool-multiplier must be positive")
    return [float(band) for band in delta_bands]


def main() -> int:
    args = _parse_args()
    delta_bands = _validate_parameters(args)
    warnings: list[str] = []

    try:
        bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    except Exception as exc:  # noqa: BLE001
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "route_mode": "fail-closed",
            "fail_closed": True,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": warnings,
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    for slot in slots:
        status, row = _evaluate_frame(
            slot=slot,
            snapshot=slot,
            bundle=bundle,
            top_k=int(args.top_k),
            pool_multiplier=int(args.pool_multiplier),
            zero_eps=float(args.zero_eps),
            delta_bands=delta_bands,
            random_samples=int(args.random_samples),
            structured_grid=int(args.structured_grid),
            seed=int(args.seed),
        )
        counts[status] = counts.get(status, 0) + 1
        rows.append(row)

    aggregate = _aggregate_rows(rows, delta_bands=delta_bands)
    status = OK_STATUS if counts.get(PARTIAL_STATUS, 0) == 0 and counts.get(ERROR_STATUS, 0) == 0 else PARTIAL_STATUS
    if not rows:
        status = PARTIAL_STATUS
        aggregate["processed_frames"] = 0

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "route_mode": "fail-closed",
        "fail_closed": True,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
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
            "delta_bands": [float(band) for band in delta_bands],
            "random_samples": int(args.random_samples),
            "structured_grid": int(args.structured_grid),
            "seed": int(args.seed),
        },
        "status": status,
        "warnings": warnings,
        "errors": [],
        "aggregate": aggregate,
        "low_frustration_basin_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
