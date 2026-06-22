#!/usr/bin/env python3
"""Summarize the active NS triad Wall 1 shell-level telemetry surfaces."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_wall1_shell_bridge_summary.py"
CONTRACT = "ns_triad_wall1_shell_bridge_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_WALL1_SHELL_BRIDGE_SUMMARY"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_PHASE_REGIME_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_phase_regime_separation_scan_N128_20260621.json"
)
DEFAULT_FRAME_STABILITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frame_stability_scan_N128_20260621.json"
)
DEFAULT_COCYCLE_FLOOR_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cocycle_floor_scan_N128_20260621.json"
)
DEFAULT_CYCLE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_obstruction_scan_N128_20260621.json"
)
DEFAULT_HESSIAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_low_frustration_hessian_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_wall1_shell_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Summarize the active NS triad Wall 1 shell-level telemetry surfaces.",
    "R": (
        "Join the shell-indexed phase-regime, frame-stability, cocycle-floor, cycle-obstruction, "
        "and Hessian basin outputs into one compact fail-closed Wall 1 summary."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only shell bridge summary; all outputs remain empirical and non-promoting.",
    "L": (
        "Read each shell-level JSON surface, normalize onto shared frame-shell keys, "
        "compute compact correlations, and emit explicit unproved Wall 1 markers."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this bridge summary.",
    "F": "Wall 1 remains unproved; this summary only sharpens the finite-dimensional telemetry surface.",
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
    parser.add_argument("--phase-regime-json", type=Path, default=DEFAULT_PHASE_REGIME_JSON)
    parser.add_argument("--frame-stability-json", type=Path, default=DEFAULT_FRAME_STABILITY_JSON)
    parser.add_argument("--cocycle-floor-json", type=Path, default=DEFAULT_COCYCLE_FLOOR_JSON)
    parser.add_argument("--cycle-json", type=Path, default=DEFAULT_CYCLE_JSON)
    parser.add_argument("--hessian-json", type=Path, default=DEFAULT_HESSIAN_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: payload must be object")
    return payload


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value)
    return None


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in (
        "rows",
        "phase_regime_separation_rows",
        "triad_frame_stability_rows",
        "triad_cycle_obstruction_rows",
        "low_frustration_hessian_rows",
    ):
        value = payload.get(key)
        if isinstance(value, list):
            return value
    return []


def _frame_shell_key(row: dict[str, Any]) -> tuple[int, int] | None:
    frame = _coerce_int(row.get("frame"))
    shell = _coerce_int(row.get("shell"))
    if shell is None:
        shell = _coerce_int(row.get("shell_n"))
    if frame is None or shell is None:
        return None
    return int(frame), int(shell)


def _frame_key(row: dict[str, Any]) -> int | None:
    return _coerce_int(row.get("frame"))


def _pearson(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    dx = [x - mean_x for x in xs]
    dy = [y - mean_y for y in ys]
    denom_x = math.sqrt(sum(v * v for v in dx))
    denom_y = math.sqrt(sum(v * v for v in dy))
    if denom_x <= 0.0 or denom_y <= 0.0:
        return None
    return sum(a * b for a, b in zip(dx, dy)) / (denom_x * denom_y)


def _mean(values: list[float]) -> float | None:
    return float(sum(values) / len(values)) if values else None


def main() -> int:
    args = _parse_args()
    phase_payload = _read_json(args.phase_regime_json)
    frame_payload = _read_json(args.frame_stability_json)
    cocycle_payload = _read_json(args.cocycle_floor_json)
    cycle_payload = _read_json(args.cycle_json)
    hessian_payload = _read_json(args.hessian_json)

    phase_by_key = {key: row for row in _rows(phase_payload) if (key := _frame_shell_key(row)) is not None}
    cocycle_by_key = {key: row for row in _rows(cocycle_payload) if (key := _frame_shell_key(row)) is not None}
    frame_by_frame = {key: row for row in _rows(frame_payload) if (key := _frame_key(row)) is not None}
    cycle_by_frame = {key: row for row in _rows(cycle_payload) if (key := _frame_key(row)) is not None}
    hessian_by_frame = {key: row for row in _rows(hessian_payload) if (key := _frame_key(row)) is not None}

    shared_keys = sorted(set(phase_by_key) & set(cocycle_by_key))
    bridge_rows: list[dict[str, Any]] = []
    phase_eps: list[float] = []
    cocycle_bounds: list[float] = []
    floor_ratios: list[float] = []
    frame_gaps: list[float] = []

    for key in shared_keys:
        frame, shell = key
        phase_row = phase_by_key[key]
        cocycle_row = cocycle_by_key[key]
        frame_row = frame_by_frame.get(frame, {})
        cycle_row = cycle_by_frame.get(frame, {})
        hessian_row = hessian_by_frame.get(frame, {})
        phase_gap = _coerce_float(phase_row.get("optimized_lambda_gap_proxy"))
        cocycle_bound = _coerce_float(cocycle_row.get("mean_cycle_lower_bound"))
        floor_ratio = _coerce_float(cocycle_row.get("frustration_floor_ratio_vs_raw"))
        frame_margin = _coerce_float(frame_row.get("frame_stability_margin_proxy"))
        cycle_rank = _coerce_float(cycle_row.get("cycle_rank_proxy"))
        hessian_proxy = _coerce_float(hessian_row.get("best_reference_hessian_proxy"))
        bridge_rows.append(
            {
                "frame": int(frame),
                "shell": int(shell),
                "optimized_lambda_gap_proxy": phase_gap,
                "optimized_lambda_max_proxy": _coerce_float(phase_row.get("optimized_lambda_max_proxy")),
                "random_lambda_max_proxy_mean": _coerce_float(phase_row.get("random_lambda_max_proxy_mean")),
                "frustration_floor_ratio_vs_raw": floor_ratio,
                "mean_cycle_lower_bound": cocycle_bound,
                "frame_stability_margin_proxy": frame_margin,
                "cycle_rank_proxy": cycle_rank,
                "best_reference_hessian_proxy": hessian_proxy,
            }
        )
        if phase_gap is not None and cocycle_bound is not None:
            phase_eps.append(phase_gap)
            cocycle_bounds.append(cocycle_bound)
        if floor_ratio is not None:
            floor_ratios.append(floor_ratio)
        if frame_margin is not None:
            frame_gaps.append(frame_margin)

    payload = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "authority": AUTHORITY,
        "inputs": {
            "phase_regime_json": str(args.phase_regime_json),
            "frame_stability_json": str(args.frame_stability_json),
            "cocycle_floor_json": str(args.cocycle_floor_json),
            "cycle_json": str(args.cycle_json),
            "hessian_json": str(args.hessian_json),
        },
        "rows": bridge_rows,
        "aggregate": {
            "shared_frame_shell_count": int(len(shared_keys)),
            "shared_frame_count": int(len({frame for frame, _ in shared_keys})),
            "optimized_lambda_gap_proxy_mean": _mean(phase_eps),
            "mean_cycle_lower_bound_mean": _mean(cocycle_bounds),
            "frustration_floor_ratio_vs_raw_mean": _mean(floor_ratios),
            "frame_stability_margin_proxy_mean": _mean(frame_gaps),
            "phase_gap_vs_cycle_bound_correlation": _pearson(phase_eps, cocycle_bounds),
            "phase_gap_vs_frame_margin_correlation": _pearson(phase_eps, frame_gaps),
            "floor_ratio_vs_frame_margin_correlation": _pearson(floor_ratios, frame_gaps[: len(floor_ratios)])
            if floor_ratios and len(frame_gaps) == len(floor_ratios)
            else None,
            "wall1_status": "unproved",
            "theorem_authority": False,
            "clay_authority": False,
        },
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
