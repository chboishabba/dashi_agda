#!/usr/bin/env python3
"""Scan phase-regime separation for the active NS triad Wall 1 route.

This is a candidate-only, fail-closed producer. It reuses the local selected-
mode carrier, resonant triad construction, and fitted phase-field machinery
from the existing NS triad scripts, then compares random-phase baselines
against optimized low-frustration references on small shell cutoffs.

The emitted telemetry is empirical only. It does not promote any theorem, Clay
claim, or route closure; it only reports shellwise phase-regime separation
proxies, epsilon gaps, and frustration-floor ratios.
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
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_SEED,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    ReferenceSpec,
    _build_triad_links,
    _collect_modes,
    _fit_phase_field,
    _frame_velocity,
    _fraction,
    _json_text,
    _load_raw_bundle,
    _mode_arrays,
    _reference_shift,
    _reference_specs,
    _score_shift_batch,
    _scalar_vorticity_spectrum,
    _weighted_quantile,
    _wrap_phase_array,
)


SCRIPT_NAME = "scripts/ns_triad_phase_regime_separation_scan.py"
CONTRACT = "ns_triad_phase_regime_separation_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_PHASE_REGIME_SEPARATION_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_phase_regime_separation_scan_N128_20260621.json"
)
DEFAULT_SHELLS = (2, 3)
DEFAULT_RANDOM_SAMPLES = 256

CONTROL_CARD = {
    "O": "Measure phase-regime separation for the active NS triad Wall 1 route.",
    "R": (
        "Compare random-phase baselines against optimized low-frustration references "
        "on small shell cutoffs and summarize the separation signal."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; the phase-regime proxies are empirical only.",
    "L": (
        "Load raw frames, reuse the selected Fourier-vorticity triad machinery, "
        "and compare random-phase versus optimized low-frustration shell carriers."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "This scan estimates separation and epsilon-gap proxies only; it does not prove closure.",
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
    parser.add_argument("--random-samples", type=int, default=DEFAULT_RANDOM_SAMPLES)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


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


def _validate_parameters(args: argparse.Namespace) -> list[int]:
    shells = _validate_shells(args.shells)
    if int(args.random_samples) <= 0:
        raise SystemExit("--random-samples must be positive")
    if int(args.top_k) <= 0:
        raise SystemExit("--top-k must be positive")
    if int(args.pool_multiplier) <= 0:
        raise SystemExit("--pool-multiplier must be positive")
    return shells


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _reference_shift_rms(shift: np.ndarray) -> float:
    wrapped = np.asarray(_wrap_phase_array(shift), dtype=np.float64)
    return float(math.sqrt(float(np.mean(np.square(wrapped))))) if len(wrapped) else 0.0


def _lambda_proxy_from_floor(floor_proxy: float) -> float:
    if not math.isfinite(float(floor_proxy)):
        return 0.0
    return float(max(0.0, 1.0 - min(max(float(floor_proxy), 0.0), math.pi) / math.pi))


def _mode_shell_filter(modes: list[Any], shell_n: int) -> list[Any]:
    if not modes:
        return []
    # The selected-mode carrier lives on archive-native shell radii, so the
    # small Wall 1 shell numbers are interpreted as rank cutoffs over the
    # distinct shell levels present in the carrier rather than literal raw
    # radius values.
    shell_levels = sorted({int(getattr(mode, "shell_radius", 0)) for mode in modes})
    cutoff_levels = set(shell_levels[: max(1, min(int(shell_n), len(shell_levels)))])
    return [mode for mode in modes if int(getattr(mode, "shell_radius", 0)) in cutoff_levels]


def _random_phase_shifts(shell_mode_count: int, samples: int, seed: int) -> np.ndarray:
    if shell_mode_count <= 0 or samples <= 0:
        return np.zeros((0, max(shell_mode_count, 0)), dtype=np.float64)
    rng = np.random.default_rng(int(seed))
    return np.asarray(
        rng.uniform(low=-math.pi, high=math.pi, size=(int(samples), int(shell_mode_count))),
        dtype=np.float64,
    )


def _candidate_rows(
    modes: list[Any],
    triad_links: list[Any],
    zero_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    amplitudes, phases, _, shell_coord = _mode_arrays(modes)
    fitted_phase, _, _, _, phase_field_fit_rmse = _fit_phase_field(modes, zero_eps=zero_eps)

    if not triad_links:
        return [], {
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
        floor_proxy = float(scores["score_mean_abs"][0])
        floor_rmse = float(scores["score_rmse"][0])
        lambda_proxy = float(scores["score_coherence"][0])
        alignment_fraction = float(scores["score_alignment_fraction"][0])
        floor_ratio = _fraction(floor_proxy, math.pi)
        candidate_rows.append(
            {
                "reference_id": spec.reference_id,
                "reference_kind": spec.reference_kind,
                "phase_slope": float(spec.phase_slope),
                "phase_offset": float(_wrap_phase_array(offset)),
                "phase_shift_rms": _reference_shift_rms(np.asarray(shift, dtype=np.float64)),
                "frustration_floor_proxy": floor_proxy,
                "frustration_floor_rmse": floor_rmse,
                "frustration_floor_ratio": float(floor_ratio),
                "lambda_max_proxy": lambda_proxy,
                "lambda_gap_proxy": float(max(0.0, 1.0 - lambda_proxy)),
                "triad_phase_alignment_fraction": alignment_fraction,
                "triad_count": int(len(triad_links)),
            }
        )

    candidate_rows.sort(
        key=lambda row: (
            float(row["frustration_floor_proxy"]),
            -float(row["lambda_max_proxy"]),
            float(row["phase_shift_rms"]),
        )
    )
    for rank, row in enumerate(candidate_rows, start=1):
        row["reference_rank"] = int(rank)

    return candidate_rows, {
        "phase_field_fit_rmse": float(phase_field_fit_rmse),
        "fitted_phase": np.asarray(fitted_phase, dtype=np.float64),
        "shell_coord": np.asarray(shell_coord, dtype=np.float64),
        "amplitudes": np.asarray(amplitudes, dtype=np.float64),
        "phases": np.asarray(phases, dtype=np.float64),
        "weights": weights,
        "left_idx": left_idx,
        "right_idx": right_idx,
        "out_idx": out_idx,
        "total_weight": float(total_weight),
    }


def _random_phase_summary(
    phases: np.ndarray,
    left_idx: np.ndarray,
    right_idx: np.ndarray,
    out_idx: np.ndarray,
    weights: np.ndarray,
    random_samples: int,
    seed: int,
    zero_eps: float,
) -> dict[str, Any]:
    random_shifts = _random_phase_shifts(len(phases), int(random_samples), int(seed))
    scores = _score_shift_batch(
        phases=phases,
        shifts=random_shifts,
        left_idx=left_idx,
        right_idx=right_idx,
        out_idx=out_idx,
        weights=weights,
        zero_eps=zero_eps,
    )
    lambda_values = np.asarray(scores["score_coherence"], dtype=np.float64)
    floor_values = np.asarray(scores["score_mean_abs"], dtype=np.float64)
    rmse_values = np.asarray(scores["score_rmse"], dtype=np.float64)
    alignment_values = np.asarray(scores["score_alignment_fraction"], dtype=np.float64)
    if len(lambda_values) == 0:
        return {
            "sample_count": 0,
            "lambda_max_proxy_mean": 0.0,
            "lambda_max_proxy_p95": 0.0,
            "lambda_max_proxy_best": 0.0,
            "lambda_gap_proxy_mean": 1.0,
            "frustration_floor_proxy_mean": 0.0,
            "frustration_floor_proxy_p95": 0.0,
            "frustration_floor_proxy_best": 0.0,
            "frustration_floor_rmse_mean": 0.0,
            "triad_phase_alignment_fraction_mean": 0.0,
        }
    return {
        "sample_count": int(len(lambda_values)),
        "lambda_max_proxy_mean": float(np.mean(lambda_values)),
        "lambda_max_proxy_p95": float(np.quantile(lambda_values, 0.95)),
        "lambda_max_proxy_best": float(np.max(lambda_values)),
        "lambda_gap_proxy_mean": float(np.mean(1.0 - lambda_values)),
        "frustration_floor_proxy_mean": float(np.mean(floor_values)),
        "frustration_floor_proxy_p95": float(np.quantile(floor_values, 0.95)),
        "frustration_floor_proxy_best": float(np.min(floor_values)),
        "frustration_floor_rmse_mean": float(np.mean(rmse_values)),
        "triad_phase_alignment_fraction_mean": float(np.mean(alignment_values)),
    }


def _shell_row(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    shell_n: int,
    random_samples: int,
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
        "shell_n": int(shell_n),
        "route_family": "Wall 1",
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
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
        shell_modes = _mode_shell_filter(modes, shell_n=shell_n)
        triad_links = _build_triad_links(shell_modes, zero_eps=zero_eps)
        candidate_rows, derived = _candidate_rows(shell_modes, triad_links, zero_eps=zero_eps)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_triad_phase_regime_separation_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(len(modes)),
            "shell_mode_count": int(len(shell_modes)),
            "selected_mode_amplitude_sum": float(sum(mode.amplitude for mode in shell_modes)),
            "triad_count": int(len(triad_links)),
            "phase_field_fit_rmse": float(derived["phase_field_fit_rmse"]),
            "reference_candidate_count": int(len(candidate_rows)),
            "reference_candidates": candidate_rows,
        }
    )

    if not candidate_rows or not triad_links or len(shell_modes) < 3:
        row.update(
            {
                "status": PARTIAL_STATUS,
                "warnings": [
                    "shell cutoff did not yield enough resonant selected-mode triads for a stable separation estimate"
                ],
                "random_phase_sample_count": int(random_samples),
                "random_phase_lambda_max_proxy_mean": 0.0,
                "random_phase_lambda_max_proxy_p95": 0.0,
                "random_phase_lambda_max_proxy_best": 0.0,
                "random_phase_lambda_gap_proxy_mean": 1.0,
                "random_phase_frustration_floor_proxy_mean": 0.0,
                "random_phase_frustration_floor_proxy_p95": 0.0,
                "random_phase_frustration_floor_proxy_best": 0.0,
                "random_phase_frustration_floor_rmse_mean": 0.0,
                "random_phase_alignment_fraction_mean": 0.0,
                "optimized_reference_id": None,
                "optimized_reference_kind": None,
                "optimized_reference_rank": None,
                "optimized_frustration_floor_proxy": None,
                "optimized_frustration_floor_rmse": None,
                "optimized_lambda_max_proxy": None,
                "optimized_lambda_gap_proxy": None,
                "optimized_epsilon_gap_proxy": None,
                "random_phase_vs_optimized_lambda_gap": None,
                "random_phase_vs_optimized_floor_ratio": None,
                "optimized_vs_random_phase_floor_ratio": None,
            }
        )
        return PARTIAL_STATUS, row

    weights = np.asarray(derived["weights"], dtype=np.float64)
    left_idx = np.asarray(derived["left_idx"], dtype=np.int64)
    right_idx = np.asarray(derived["right_idx"], dtype=np.int64)
    out_idx = np.asarray(derived["out_idx"], dtype=np.int64)
    phases = np.asarray(derived["phases"], dtype=np.float64)
    shell_coord = np.asarray(derived["shell_coord"], dtype=np.float64)
    amplitudes = np.asarray(derived["amplitudes"], dtype=np.float64)
    fitted_phase = np.asarray(derived["fitted_phase"], dtype=np.float64)

    random_summary = _random_phase_summary(
        phases=phases,
        left_idx=left_idx,
        right_idx=right_idx,
        out_idx=out_idx,
        weights=weights,
        random_samples=int(random_samples),
        seed=int(seed + slot * 10007 + shell_n * 1009),
        zero_eps=zero_eps,
    )

    optimized = candidate_rows[0]
    zero_row = next((row_ for row_ in candidate_rows if row_["reference_id"] == "zero"), None)
    best_global = next((row_ for row_ in candidate_rows if row_["reference_kind"] == "global"), None)
    best_structured = next((row_ for row_ in candidate_rows if row_["reference_kind"] == "structured"), None)

    optimized_lambda = float(optimized["lambda_max_proxy"])
    optimized_floor = float(optimized["frustration_floor_proxy"])
    random_lambda_mean = float(random_summary["lambda_max_proxy_mean"])
    random_floor_mean = float(random_summary["frustration_floor_proxy_mean"])

    row.update(
        {
            "status": OK_STATUS,
            "random_phase_sample_count": int(random_summary["sample_count"]),
            "random_phase_lambda_max_proxy_mean": random_lambda_mean,
            "random_phase_lambda_max_proxy_p95": float(random_summary["lambda_max_proxy_p95"]),
            "random_phase_lambda_max_proxy_best": float(random_summary["lambda_max_proxy_best"]),
            "random_phase_lambda_gap_proxy_mean": float(random_summary["lambda_gap_proxy_mean"]),
            "random_phase_frustration_floor_proxy_mean": random_floor_mean,
            "random_phase_frustration_floor_proxy_p95": float(random_summary["frustration_floor_proxy_p95"]),
            "random_phase_frustration_floor_proxy_best": float(random_summary["frustration_floor_proxy_best"]),
            "random_phase_frustration_floor_rmse_mean": float(random_summary["frustration_floor_rmse_mean"]),
            "random_phase_alignment_fraction_mean": float(random_summary["triad_phase_alignment_fraction_mean"]),
            "optimized_reference_id": optimized["reference_id"],
            "optimized_reference_kind": optimized["reference_kind"],
            "optimized_reference_rank": int(optimized["reference_rank"]),
            "optimized_reference_phase_slope": float(optimized["phase_slope"]),
            "optimized_reference_phase_offset": float(optimized["phase_offset"]),
            "optimized_reference_phase_shift_rms": float(optimized["phase_shift_rms"]),
            "optimized_frustration_floor_proxy": optimized_floor,
            "optimized_frustration_floor_rmse": float(optimized["frustration_floor_rmse"]),
            "optimized_lambda_max_proxy": optimized_lambda,
            "optimized_lambda_gap_proxy": float(optimized["lambda_gap_proxy"]),
            "optimized_epsilon_gap_proxy": float(max(0.0, 1.0 - optimized_lambda)),
            "optimized_phase_alignment_fraction": float(optimized["triad_phase_alignment_fraction"]),
            "optimized_vs_random_phase_lambda_gap": float(optimized_lambda - random_lambda_mean),
            "optimized_vs_random_phase_lambda_ratio": float(optimized_lambda / max(random_lambda_mean, 1.0e-12)),
            "optimized_vs_random_phase_floor_ratio": float(optimized_floor / max(random_floor_mean, 1.0e-12)),
            "random_phase_vs_optimized_floor_ratio": float(random_floor_mean / max(optimized_floor, 1.0e-12)),
            "phase_regime_separation_score": float(optimized_lambda - random_lambda_mean),
            "phase_regime_separation_ratio": float(optimized_lambda / max(random_lambda_mean, 1.0e-12)),
            "lambda_gap_floor_ratio": float(optimized["lambda_gap_proxy"] / max(optimized_floor / math.pi, 1.0e-12)),
            "zero_reference_frustration_floor_proxy": float(zero_row["frustration_floor_proxy"]) if zero_row else None,
            "zero_reference_lambda_max_proxy": float(zero_row["lambda_max_proxy"]) if zero_row else None,
            "best_global_reference_id": best_global.get("reference_id") if best_global else None,
            "best_global_reference_rank": int(best_global["reference_rank"]) if best_global else None,
            "best_global_lambda_max_proxy": float(best_global["lambda_max_proxy"]) if best_global else None,
            "best_structured_reference_id": best_structured.get("reference_id") if best_structured else None,
            "best_structured_reference_rank": int(best_structured["reference_rank"]) if best_structured else None,
            "best_structured_lambda_max_proxy": float(best_structured["lambda_max_proxy"]) if best_structured else None,
            "shell_coord_mean": float(np.mean(shell_coord)) if len(shell_coord) else 0.0,
            "shell_coord_span": float(np.max(shell_coord) - np.min(shell_coord)) if len(shell_coord) else 0.0,
            "selected_mode_amplitude_sum": float(sum(mode.amplitude for mode in shell_modes)),
            "triad_weight_sum": float(np.sum(weights)),
            "phase_field_fit_rmse": float(derived["phase_field_fit_rmse"]),
            "shell_mode_count_ratio": _fraction(float(len(shell_modes)), float(len(modes))),
        }
    )
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]], shells: list[int]) -> dict[str, Any]:
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

    shell_aggregates: list[dict[str, Any]] = []
    for shell_n in shells:
        shell_rows = [row for row in ok_rows if int(row.get("shell_n", 0)) == int(shell_n)]
        if not shell_rows:
            shell_aggregates.append(
                {
                    "shell_n": int(shell_n),
                    "frame_count": 0,
                    "lambda_max_proxy_mean": None,
                    "random_phase_lambda_max_proxy_mean": None,
                    "optimized_epsilon_gap_proxy_mean": None,
                    "optimized_vs_random_phase_lambda_gap_mean": None,
                    "optimized_vs_random_phase_floor_ratio_mean": None,
                    "phase_regime_separation_score_mean": None,
                }
            )
            continue
        shell_aggregates.append(
            {
                "shell_n": int(shell_n),
                "frame_count": int(len(shell_rows)),
                "lambda_max_proxy_mean": float(np.mean([row.get("optimized_lambda_max_proxy", 0.0) for row in shell_rows])),
                "random_phase_lambda_max_proxy_mean": float(
                    np.mean([row.get("random_phase_lambda_max_proxy_mean", 0.0) for row in shell_rows])
                ),
                "optimized_epsilon_gap_proxy_mean": float(
                    np.mean([row.get("optimized_epsilon_gap_proxy", 0.0) for row in shell_rows])
                ),
                "optimized_vs_random_phase_lambda_gap_mean": float(
                    np.mean([row.get("optimized_vs_random_phase_lambda_gap", 0.0) for row in shell_rows])
                ),
                "optimized_vs_random_phase_floor_ratio_mean": float(
                    np.mean([row.get("optimized_vs_random_phase_floor_ratio", 0.0) for row in shell_rows])
                ),
                "phase_regime_separation_score_mean": float(
                    np.mean([row.get("phase_regime_separation_score", 0.0) for row in shell_rows])
                ),
            }
        )

    optimized_lambda = _series("optimized_lambda_max_proxy")
    random_lambda = _series("random_phase_lambda_max_proxy_mean")
    optimized_gap = _series("optimized_epsilon_gap_proxy")
    random_floor = _series("random_phase_frustration_floor_proxy_mean")
    optimized_floor = _series("optimized_frustration_floor_proxy")
    separation_score = _series("phase_regime_separation_score")

    return {
        "processed_frames": len(rows),
        "ok_frames": len(ok_rows),
        "partial_frames": len(partial_rows),
        "error_frames": len(error_rows),
        "shell_count": int(len(shells)),
        "shells": [int(shell) for shell in shells],
        "top_k": int(ok_rows[0]["top_k"]) if ok_rows else None,
        "pool_multiplier": int(ok_rows[0]["pool_multiplier"]) if ok_rows else None,
        "zero_eps": float(ok_rows[0]["zero_eps"]) if ok_rows else None,
        "random_samples": int(ok_rows[0]["random_phase_sample_count"]) if ok_rows else None,
        "selected_mode_count_mean": float(np.mean([row.get("selected_mode_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "shell_mode_count_mean": float(np.mean([row.get("shell_mode_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_count_mean": float(np.mean([row.get("triad_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_count_total": int(sum(int(row.get("triad_count", 0)) for row in ok_rows)),
        "phase_field_fit_rmse_mean": float(np.mean([row.get("phase_field_fit_rmse", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "optimized_lambda_max_proxy_mean": float(np.mean(optimized_lambda)) if optimized_lambda else 0.0,
        "random_phase_lambda_max_proxy_mean": float(np.mean(random_lambda)) if random_lambda else 0.0,
        "optimized_epsilon_gap_proxy_mean": float(np.mean(optimized_gap)) if optimized_gap else 0.0,
        "optimized_frustration_floor_proxy_mean": float(np.mean(optimized_floor)) if optimized_floor else 0.0,
        "random_phase_frustration_floor_proxy_mean": float(np.mean(random_floor)) if random_floor else 0.0,
        "phase_regime_separation_score_mean": float(np.mean(separation_score)) if separation_score else 0.0,
        "optimized_vs_random_phase_lambda_gap_mean": float(
            np.mean([row.get("optimized_vs_random_phase_lambda_gap", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "optimized_vs_random_phase_lambda_ratio_mean": float(
            np.mean([row.get("optimized_vs_random_phase_lambda_ratio", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "optimized_vs_random_phase_floor_ratio_mean": float(
            np.mean([row.get("optimized_vs_random_phase_floor_ratio", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "random_phase_vs_optimized_floor_ratio_mean": float(
            np.mean([row.get("random_phase_vs_optimized_floor_ratio", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "shell_mode_fraction_mean": float(np.mean([row.get("shell_mode_count_ratio", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "lambda_gap_floor_ratio_mean": float(np.mean([row.get("lambda_gap_floor_ratio", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "lambda_max_vs_random_correlation": _pearson(
            [float(row.get("optimized_lambda_max_proxy", 0.0)) for row in ok_rows],
            [float(row.get("random_phase_lambda_max_proxy_mean", 0.0)) for row in ok_rows],
        ),
        "lambda_gap_vs_floor_correlation": _pearson(
            [float(row.get("optimized_epsilon_gap_proxy", 0.0)) for row in ok_rows],
            [float(row.get("optimized_frustration_floor_proxy", 0.0)) for row in ok_rows],
        ),
        "shell_n_vs_lambda_gap_correlation": _pearson(
            [float(row.get("shell_n", 0.0)) for row in ok_rows],
            [float(row.get("optimized_epsilon_gap_proxy", 0.0)) for row in ok_rows],
        ),
        "shell_n_vs_separation_score_correlation": _pearson(
            [float(row.get("shell_n", 0.0)) for row in ok_rows],
            [float(row.get("phase_regime_separation_score", 0.0)) for row in ok_rows],
        ),
        "shell_aggregates": shell_aggregates,
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_parameters(args)
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
            "phase_regime_separation_rows": [],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty)
        args.output_json.write_text(text + "\n", encoding="utf-8")
        print(text)
        return 1

    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    if not slots:
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
            "errors": ["no frames selected for triad phase-regime separation scan"],
            "warnings": warnings,
            "phase_regime_separation_rows": [],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(payload, args.pretty)
        args.output_json.write_text(text + "\n", encoding="utf-8")
        print(text)
        return 1

    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    for slot in slots:
        for shell_n in shells:
            status, row = _shell_row(
                slot=slot,
                snapshot=slot,
                bundle=bundle,
                top_k=int(args.top_k),
                pool_multiplier=int(args.pool_multiplier),
                zero_eps=float(args.zero_eps),
                shell_n=int(shell_n),
                random_samples=int(args.random_samples),
                seed=int(args.seed),
            )
            counts[status] = counts.get(status, 0) + 1
            rows.append(row)

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
            "shells": shells,
            "random_samples": int(args.random_samples),
            "seed": int(args.seed),
        },
        "status": OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 and counts.get(PARTIAL_STATUS, 0) == 0 else PARTIAL_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": _aggregate_rows(rows, shells),
        "phase_regime_separation_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = _json_text(payload, args.pretty)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
