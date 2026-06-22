#!/usr/bin/env python3
"""Scan cocycle-frustration floor proxies for the active NS triad Wall 1 route."""

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


def _wrap_phase(angle: float) -> float:
    wrapped = (float(angle) + math.pi) % (2.0 * math.pi) - math.pi
    if wrapped <= -math.pi:
        wrapped += 2.0 * math.pi
    return float(wrapped)


def _choose_best_reference(
    phases: np.ndarray,
    amplitudes: np.ndarray,
    shell_coord: np.ndarray,
    fitted_phase: np.ndarray,
    triad_links: list[Any],
    zero_eps: float,
) -> tuple[dict[str, Any], np.ndarray]:
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
    return best, shift


def _cycle_lower_bounds(
    incidence: np.ndarray,
    weights: np.ndarray,
    closures: np.ndarray,
    zero_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, float]]:
    triad_count = int(len(weights))
    if triad_count == 0 or incidence.size == 0:
        return [], {
            "cycle_rank": 0.0,
            "defective_cycle_count": 0.0,
            "max_cycle_lower_bound": 0.0,
            "mean_cycle_lower_bound": 0.0,
            "cycle_lower_bound_sum": 0.0,
            "cocycle_defect_mean": 0.0,
            "cocycle_defect_max": 0.0,
        }

    try:
        _, singular_values, vt = np.linalg.svd(incidence.T, full_matrices=True)
    except np.linalg.LinAlgError:
        return [], {
            "cycle_rank": 0.0,
            "defective_cycle_count": 0.0,
            "max_cycle_lower_bound": 0.0,
            "mean_cycle_lower_bound": 0.0,
            "cycle_lower_bound_sum": 0.0,
            "cocycle_defect_mean": 0.0,
            "cocycle_defect_max": 0.0,
        }

    tol = max(float(zero_eps) * 1000.0, 1.0e-10)
    rank = int(np.sum(singular_values > tol))
    nullity = max(0, triad_count - rank)
    if nullity <= 0:
        return [], {
            "cycle_rank": float(nullity),
            "defective_cycle_count": 0.0,
            "max_cycle_lower_bound": 0.0,
            "mean_cycle_lower_bound": 0.0,
            "cycle_lower_bound_sum": 0.0,
            "cocycle_defect_mean": 0.0,
            "cocycle_defect_max": 0.0,
        }

    basis = np.asarray(vt[-nullity:], dtype=np.float64)
    records: list[dict[str, Any]] = []
    lower_bounds: list[float] = []
    defects: list[float] = []

    for cycle_index, vector in enumerate(basis):
        dual_norm = float(np.sum((vector * vector) / np.maximum(weights, float(zero_eps))))
        raw_defect = float(np.dot(vector, closures))
        defect = abs(math.remainder(raw_defect, 2.0 * math.pi))
        if defect > math.pi:
            defect = abs(defect - 2.0 * math.pi)
        lower_bound = 0.0
        if dual_norm > float(zero_eps):
            lower_bound = float((4.0 / (math.pi * math.pi)) * (defect * defect) / dual_norm)
        records.append(
            {
                "cycle_index": int(cycle_index),
                "cycle_dual_norm": float(dual_norm),
                "cycle_raw_defect": float(raw_defect),
                "cycle_defect": float(defect),
                "cycle_lower_bound": float(lower_bound),
            }
        )
        lower_bounds.append(float(lower_bound))
        defects.append(float(defect))

    defective_count = sum(1 for value in defects if value > float(zero_eps))
    return records, {
        "cycle_rank": float(nullity),
        "defective_cycle_count": float(defective_count),
        "max_cycle_lower_bound": float(max(lower_bounds, default=0.0)),
        "mean_cycle_lower_bound": float(np.mean(lower_bounds)) if lower_bounds else 0.0,
        "cycle_lower_bound_sum": float(np.sum(lower_bounds)) if lower_bounds else 0.0,
        "cocycle_defect_mean": float(np.mean(defects)) if defects else 0.0,
        "cocycle_defect_max": float(max(defects, default=0.0)),
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
        best_reference, best_shift = _choose_best_reference(
            phases=phases,
            amplitudes=amplitudes,
            shell_coord=shell_coord,
            fitted_phase=fitted_phase,
            triad_links=triad_links,
            zero_eps=zero_eps,
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
            closures=adjusted_closures,
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
            "shell_spread_mean": float(np.mean(shell_spreads)) if len(shell_spreads) else 0.0,
            "distinct_shell_count_mean": float(np.mean(distinct_shells)) if len(distinct_shells) else 0.0,
            "cycle_rank_proxy": float(cycle_metrics["cycle_rank"]),
            "defective_cycle_count": float(cycle_metrics["defective_cycle_count"]),
            "max_cycle_lower_bound": float(cycle_metrics["max_cycle_lower_bound"]),
            "mean_cycle_lower_bound": float(cycle_metrics["mean_cycle_lower_bound"]),
            "cycle_lower_bound_sum": float(cycle_metrics["cycle_lower_bound_sum"]),
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
        "mean_cycle_lower_bound_mean": float(np.mean(_series("mean_cycle_lower_bound"))) if _series("mean_cycle_lower_bound") else None,
        "max_cycle_lower_bound_mean": float(np.mean(_series("max_cycle_lower_bound"))) if _series("max_cycle_lower_bound") else None,
        "frustration_floor_ratio_vs_raw_mean": float(np.mean(_series("frustration_floor_ratio_vs_raw")))
        if _series("frustration_floor_ratio_vs_raw")
        else None,
        "best_reference_lambda_max_proxy_mean": float(np.mean(_series("best_reference_lambda_max_proxy")))
        if _series("best_reference_lambda_max_proxy")
        else None,
        "cocycle_defect_mean_mean": float(np.mean(_series("cocycle_defect_mean"))) if _series("cocycle_defect_mean") else None,
        "cycle_rank_vs_floor_ratio_correlation": _pearson(
            _series("cycle_rank_proxy"),
            _series("frustration_floor_ratio_vs_raw"),
        ),
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells)
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    frame_indices = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)

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
