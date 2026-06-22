#!/usr/bin/env python3
"""Empirically scan low-frustration triad Hessian telemetry.

This producer reuses the selected-mode triad carrier from the basin scan, but
scores candidate phase references with a weighted second-moment proxy rather
than the first-moment floor proxy. The output stays candidate-only and
fail-closed: it is a telemetry surface for the Wall 1 Hessian / backbone route,
not a theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_low_frustration_basin_scan import (  # type: ignore
    ALLOWED_STATUSES,
    AUTHORITY,
    DEFAULT_DELTA_BANDS,
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RANDOM_SAMPLES,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_SEED,
    DEFAULT_STRUCTURED_GRID,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    ERROR_STATUS,
    NEGATIVE_LOG_VOLUME_EPS,
    OK_STATUS,
    PARTIAL_STATUS,
    ReferenceSpec,
    TriadLink,
    _build_triad_links,
    _collect_modes,
    _finite_float,
    _fit_phase_field,
    _frame_velocity,
    _fraction,
    _json_text,
    _load_raw_bundle,
    _mode_arrays,
    _parse_args as _unused_basin_parse_args,
    _random_shifts,
    _reference_shift,
    _reference_specs,
    _scalar_vorticity_spectrum,
    _structured_shifts,
    _weighted_quantile,
    _wrap_phase_array,
)


SCRIPT_NAME = "scripts/ns_triad_low_frustration_hessian_scan.py"
CONTRACT = "ns_triad_low_frustration_hessian_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_LOW_FRUSTRATION_HESSIAN_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_low_frustration_hessian_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Empirically scan low-frustration triad Hessian telemetry around the best triad reference.",
    "R": (
        "Rebuild the selected-mode triad carrier, evaluate Hessian-based basin proxies, "
        "and probe how thin the low-frustration basin looks under perturbations."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; Hessian norms and basin proxies are empirical only.",
    "L": (
        "Load raw frames, reuse the selected Fourier-vorticity triad machinery, choose the best "
        "reference, and sample random plus structured perturbations around it."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, residence-time exclusion, or promotion claim is inferred.",
    "F": "This scan estimates Hessian-based basin structure only; it does not prove exclusion or closure.",
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
        "--delta-band",
        dest="delta_bands",
        action="append",
        type=float,
        default=None,
        help="Absolute perturbation band in radians; may be repeated.",
    )
    parser.add_argument("--random-samples", type=int, default=DEFAULT_RANDOM_SAMPLES)
    parser.add_argument("--structured-grid", type=int, default=DEFAULT_STRUCTURED_GRID)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


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
            "score_second_moment": empty,
            "score_rmse": empty,
            "score_coherence": empty,
            "score_alignment_fraction": empty,
            "residual": np.zeros((0, len(weights)), dtype=np.float64),
            "residual_abs": np.zeros((0, len(weights)), dtype=np.float64),
        }

    adjusted = np.asarray(_wrap_phase_array(phases[None, :] - shifts), dtype=np.float64)
    residuals = np.asarray(
        _wrap_phase_array(adjusted[:, left_idx] + adjusted[:, right_idx] - adjusted[:, out_idx]),
        dtype=np.float64,
    )
    abs_residuals = np.abs(residuals)
    total_weight = float(np.sum(weights))
    if total_weight <= 0.0 or not math.isfinite(total_weight):
        total_weight = 1.0

    weighted_abs = np.sum(abs_residuals * weights[None, :], axis=1) / total_weight
    weighted_second_moment = np.sum((residuals * residuals) * weights[None, :], axis=1) / total_weight
    weighted_rmse = np.sqrt(weighted_second_moment)
    weighted_complex = np.sum(np.exp(1j * residuals) * weights[None, :], axis=1)
    coherence = np.abs(weighted_complex) / total_weight
    alignment = np.sum((abs_residuals <= float(zero_eps)) * weights[None, :], axis=1) / total_weight
    return {
        "score_mean_abs": np.asarray(weighted_abs, dtype=np.float64),
        "score_second_moment": np.asarray(weighted_second_moment, dtype=np.float64),
        "score_rmse": np.asarray(weighted_rmse, dtype=np.float64),
        "score_coherence": np.asarray(coherence, dtype=np.float64),
        "score_alignment_fraction": np.asarray(alignment, dtype=np.float64),
        "residual": np.asarray(residuals, dtype=np.float64),
        "residual_abs": np.asarray(abs_residuals, dtype=np.float64),
    }


def _candidate_rows(
    modes: list[Any],
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
        residual = np.asarray(scores["residual"][0], dtype=np.float64)
        abs_residual = np.asarray(scores["residual_abs"][0], dtype=np.float64)
        hessian_proxy = float(scores["score_second_moment"][0])
        hessian_rmse = float(scores["score_rmse"][0])
        hessian_p95 = float(_weighted_quantile(abs_residual, weights, 0.95))
        phase_coherence = float(scores["score_coherence"][0])
        alignment_fraction = float(scores["score_alignment_fraction"][0])
        shift_rms = (
            float(math.sqrt(float(np.mean(np.square(np.asarray(_wrap_phase_array(shift), dtype=np.float64))))))
            if len(shift)
            else 0.0
        )
        candidate_rows.append(
            {
                "reference_id": spec.reference_id,
                "reference_kind": spec.reference_kind,
                "phase_slope": float(spec.phase_slope),
                "phase_offset": float(_wrap_phase_array(offset)),
                "phase_shift_rms": shift_rms,
                "hessian_proxy": hessian_proxy,
                "hessian_rmse": hessian_rmse,
                "hessian_p95": hessian_p95,
                "triad_phase_coherence": phase_coherence,
                "phase_alignment_fraction": alignment_fraction,
                "triad_count": int(len(triad_links)),
            }
        )

    candidate_rows.sort(
        key=lambda row: (
            float(row["hessian_proxy"]),
            float(row["hessian_rmse"]),
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
        },
    )


def _delta_band_row(
    delta_band: float,
    center_shift: np.ndarray,
    shell_coord: np.ndarray,
    phases: np.ndarray,
    left_idx: np.ndarray,
    right_idx: np.ndarray,
    out_idx: np.ndarray,
    weights: np.ndarray,
    best_hessian_proxy: float,
    structured_grid: int,
    random_samples: int,
    seed: int,
) -> dict[str, Any]:
    structured_shifts = _structured_shifts(center_shift, shell_coord, delta_band=delta_band, grid=structured_grid)
    random_shifts = _random_shifts(center_shift, delta_band=delta_band, samples=random_samples, seed=seed)
    threshold = float(best_hessian_proxy + float(delta_band))

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

    structured_metric = np.asarray(structured_scores["score_second_moment"], dtype=np.float64)
    random_metric = np.asarray(random_scores["score_second_moment"], dtype=np.float64)
    structured_occupancy = _fraction(float(np.count_nonzero(structured_metric <= threshold)), float(len(structured_metric)))
    random_occupancy = _fraction(float(np.count_nonzero(random_metric <= threshold)), float(len(random_metric)))
    combined_total = float(len(structured_metric) + len(random_metric))
    combined_hits = float(
        np.count_nonzero(structured_metric <= threshold) + np.count_nonzero(random_metric <= threshold)
    )
    occupancy = _fraction(combined_hits, combined_total)
    rarity_proxy = float(-math.log(max(occupancy, NEGATIVE_LOG_VOLUME_EPS)))

    structured_mean = float(np.mean(structured_metric)) if len(structured_metric) else 0.0
    random_mean = float(np.mean(random_metric)) if len(random_metric) else 0.0
    structured_p95 = float(np.quantile(structured_metric, 0.95)) if len(structured_metric) else 0.0
    random_p95 = float(np.quantile(random_metric, 0.95)) if len(random_metric) else 0.0
    combined_p95 = (
        float(np.quantile(np.concatenate([structured_metric, random_metric]), 0.95))
        if combined_total > 0.0
        else 0.0
    )
    return {
        "delta_band": float(delta_band),
        "threshold": float(threshold),
        "structured_sample_count": int(len(structured_metric)),
        "random_sample_count": int(len(random_metric)),
        "sample_count": int(combined_total),
        "occupancy_fraction": float(occupancy),
        "structured_occupancy_fraction": float(structured_occupancy),
        "random_occupancy_fraction": float(random_occupancy),
        "negative_log_volume_proxy": float(rarity_proxy),
        "structured_minus_random_occupancy_gap": float(structured_occupancy - random_occupancy),
        "structured_minus_random_hessian_gap": float(structured_mean - random_mean),
        "structured_mean_hessian_proxy": float(structured_mean),
        "random_mean_hessian_proxy": float(random_mean),
        "combined_mean_hessian_proxy": float(
            ((structured_mean * len(structured_metric)) + (random_mean * len(random_metric))) / combined_total
        ),
        "structured_hessian_p95": float(structured_p95),
        "random_hessian_p95": float(random_p95),
        "combined_hessian_p95": float(combined_p95),
        "threshold_gap": float(delta_band),
        "structured_samples": {"family": "grid_shell_affine", "grid_size": int(structured_grid)},
        "random_samples": {"family": "gaussian_full_space", "seed": int(seed)},
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
        "reference_family": "best_reference_centered_hessian_scan",
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        modes = _collect_modes(spectrum, top_k=int(top_k), zero_eps=float(zero_eps), pool_multiplier=int(pool_multiplier))
        triad_links = _build_triad_links(modes, zero_eps=zero_eps)
        candidate_rows, zero_row, best_global, best_structured, derived = _candidate_rows(
            modes=modes,
            triad_links=triad_links,
            zero_eps=zero_eps,
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_low_frustration_hessian_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(len(modes)),
            "selected_mode_amplitude_sum": float(sum(mode.amplitude for mode in modes)),
            "triad_count": int(len(triad_links)),
            "phase_field_fit_rmse": float(derived["phase_field_fit_rmse"]),
            "reference_candidate_count": int(len(candidate_rows)),
            "reference_candidates": candidate_rows,
            "zero_reference_hessian_proxy": float(zero_row["hessian_proxy"]) if zero_row else None,
            "zero_reference_hessian_rmse": float(zero_row["hessian_rmse"]) if zero_row else None,
            "best_global_reference_id": best_global.get("reference_id") if best_global else None,
            "best_global_reference_rank": int(best_global["reference_rank"]) if best_global else None,
            "best_global_hessian_proxy": float(best_global["hessian_proxy"]) if best_global else None,
            "best_structured_reference_id": best_structured.get("reference_id") if best_structured else None,
            "best_structured_reference_rank": int(best_structured["reference_rank"]) if best_structured else None,
            "best_structured_hessian_proxy": float(best_structured["hessian_proxy"]) if best_structured else None,
        }
    )

    if not candidate_rows or not triad_links:
        row.update(
            {
                "status": PARTIAL_STATUS,
                "warnings": ["no resonant selected-mode triads found for hessian scan"],
                "delta_band_rows": [],
                "best_reference_id": None,
                "best_reference_kind": None,
                "best_reference_rank": None,
                "best_reference_phase_slope": None,
                "best_reference_phase_offset": None,
                "best_reference_phase_shift_rms": None,
                "best_reference_hessian_proxy": None,
                "best_reference_hessian_rmse": None,
                "best_reference_hessian_p95": None,
                "best_reference_phase_coherence": None,
                "best_reference_phase_alignment_fraction": None,
                "best_reference_is_zero": False,
                "best_reference_is_structured": False,
                "best_reference_is_fitted": False,
                "best_reference_hessian_improvement_over_zero": None,
                "best_reference_hessian_improvement_over_best_global": None,
                "best_structured_hessian_improvement_over_best_global": None,
                "basin_occupancy_mean": None,
                "negative_log_volume_proxy": None,
            }
        )
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
                best_hessian_proxy=float(winner["hessian_proxy"]),
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
            "best_reference_hessian_proxy": float(winner["hessian_proxy"]),
            "best_reference_hessian_rmse": float(winner["hessian_rmse"]),
            "best_reference_hessian_p95": float(winner["hessian_p95"]),
            "best_reference_phase_coherence": float(winner["triad_phase_coherence"]),
            "best_reference_phase_alignment_fraction": float(winner["phase_alignment_fraction"]),
            "best_reference_is_zero": bool(winner["reference_id"] == "zero"),
            "best_reference_is_structured": bool(winner["reference_kind"] == "structured"),
            "best_reference_is_fitted": bool(winner["reference_kind"] == "fitted"),
            "best_reference_hessian_improvement_over_zero": (
                float(zero_row["hessian_proxy"] - winner["hessian_proxy"]) if zero_row else None
            ),
            "best_reference_hessian_improvement_over_best_global": (
                float(best_global["hessian_proxy"] - winner["hessian_proxy"]) if best_global else None
            ),
            "best_structured_hessian_improvement_over_best_global": (
                float(best_global["hessian_proxy"] - best_structured["hessian_proxy"])
                if best_structured and best_global
                else None
            ),
            "delta_band_rows": delta_rows,
            "basin_occupancy_mean": float(np.mean([band["occupancy_fraction"] for band in delta_rows])) if delta_rows else 0.0,
            "negative_log_volume_proxy": float(np.mean([band["negative_log_volume_proxy"] for band in delta_rows])) if delta_rows else 0.0,
        }
    )
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]], delta_bands: list[float]) -> dict[str, Any]:
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
                    "structured_minus_random_hessian_gap_mean": None,
                    "structured_mean_hessian_proxy_mean": None,
                    "random_mean_hessian_proxy_mean": None,
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
                "structured_minus_random_hessian_gap_mean": float(
                    np.mean([row["structured_minus_random_hessian_gap"] for row in band_rows])
                ),
                "structured_mean_hessian_proxy_mean": float(np.mean([row["structured_mean_hessian_proxy"] for row in band_rows])),
                "random_mean_hessian_proxy_mean": float(np.mean([row["random_mean_hessian_proxy"] for row in band_rows])),
            }
        )

    best_hessian = _series("best_reference_hessian_proxy")
    zero_hessian = _series("zero_reference_hessian_proxy")
    basin_occupancy = _series("basin_occupancy_mean")
    rarity = _series("negative_log_volume_proxy")
    triad_count = _series("triad_count")
    selected_mode_count = _series("selected_mode_count")
    phase_field_fit_rmse = _series("phase_field_fit_rmse")
    best_improvement_over_zero = _series("best_reference_hessian_improvement_over_zero")
    best_improvement_over_global = _series("best_reference_hessian_improvement_over_best_global")
    structured_gap = _series("best_structured_hessian_improvement_over_best_global")

    return {
        "processed_frames": len(rows),
        "ok_frames": len(ok_rows),
        "partial_frames": len(partial_rows),
        "error_frames": len(error_rows),
        "reference_family": "best_reference_centered_hessian_scan",
        "top_k": int(ok_rows[0]["top_k"]) if ok_rows else None,
        "pool_multiplier": int(ok_rows[0]["pool_multiplier"]) if ok_rows else None,
        "zero_eps": float(ok_rows[0]["zero_eps"]) if ok_rows else None,
        "random_samples": int(ok_rows[0]["delta_band_rows"][0]["random_sample_count"]) if ok_rows and ok_rows[0].get("delta_band_rows") else None,
        "structured_grid": int(ok_rows[0]["delta_band_rows"][0]["structured_samples"]["grid_size"]) if ok_rows and ok_rows[0].get("delta_band_rows") else None,
        "delta_band_rows": delta_band_aggregates,
        "selected_mode_count_mean": float(np.mean(selected_mode_count)) if selected_mode_count else None,
        "triad_count_mean": float(np.mean(triad_count)) if triad_count else None,
        "phase_field_fit_rmse_mean": float(np.mean(phase_field_fit_rmse)) if phase_field_fit_rmse else None,
        "best_reference_hessian_proxy_mean": float(np.mean(best_hessian)) if best_hessian else None,
        "zero_reference_hessian_proxy_mean": float(np.mean(zero_hessian)) if zero_hessian else None,
        "best_reference_hessian_improvement_over_zero_mean": float(np.mean(best_improvement_over_zero)) if best_improvement_over_zero else None,
        "best_reference_hessian_improvement_over_best_global_mean": float(np.mean(best_improvement_over_global)) if best_improvement_over_global else None,
        "best_structured_hessian_improvement_over_best_global_mean": float(np.mean(structured_gap)) if structured_gap else None,
        "basin_occupancy_mean": float(np.mean(basin_occupancy)) if basin_occupancy else None,
        "negative_log_volume_proxy_mean": float(np.mean(rarity)) if rarity else None,
        "basin_occupancy_median": float(np.median(basin_occupancy)) if basin_occupancy else None,
        "negative_log_volume_proxy_median": float(np.median(rarity)) if rarity else None,
        "best_reference_is_zero_fraction": _fraction(float(sum(1 for row in ok_rows if row.get("best_reference_is_zero") is True)), float(len(ok_rows))) if ok_rows else None,
        "best_reference_is_structured_fraction": _fraction(float(sum(1 for row in ok_rows if row.get("best_reference_is_structured") is True)), float(len(ok_rows))) if ok_rows else None,
        "best_reference_is_fitted_fraction": _fraction(float(sum(1 for row in ok_rows if row.get("best_reference_is_fitted") is True)), float(len(ok_rows))) if ok_rows else None,
        "occupancy_vs_best_reference_hessian_correlation": _pearson(best_hessian, basin_occupancy),
        "rarity_vs_best_reference_hessian_correlation": _pearson(best_hessian, rarity),
        "triad_count_vs_basin_occupancy_correlation": _pearson(triad_count, basin_occupancy),
        "best_reference_vs_zero_hessian_correlation": _pearson(best_hessian, zero_hessian),
    }


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
        rows.append(row)
        counts[status] += 1

    aggregate = _aggregate_rows(rows, delta_bands)
    status = OK_STATUS if counts[ERROR_STATUS] == 0 and counts[PARTIAL_STATUS] == 0 else PARTIAL_STATUS
    if counts[ERROR_STATUS] == len(rows) and rows:
        status = ERROR_STATUS

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
        "status": status,
        "ok": status == OK_STATUS,
        "inputs": {
            "raw_archive": str(Path(args.raw_archive)),
            "output_json": str(args.output_json),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "random_samples": int(args.random_samples),
            "structured_grid": int(args.structured_grid),
            "seed": int(args.seed),
            "zero_eps": float(args.zero_eps),
        },
        "parameters": {
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "delta_bands": [float(band) for band in delta_bands],
            "random_samples": int(args.random_samples),
            "structured_grid": int(args.structured_grid),
            "seed": int(args.seed),
            "zero_eps": float(args.zero_eps),
        },
        "low_frustration_hessian_rows": rows,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": [],
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if status != ERROR_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
