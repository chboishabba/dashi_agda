#!/usr/bin/env python3
"""Summarize triad-incidence, frustration, and adversarial-phase telemetry.

This is a fail-closed integration surface only. It joins the shared frame keys
from the new cocycle/frustration/adversarial scans, emits compact correlations
and route metadata, and keeps the Sacasa -> triad-frustration bridge explicitly
unproved.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_frustration_bridge_summary.py"
CONTRACT = "ns_triad_frustration_bridge_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRUSTRATION_BRIDGE_SUMMARY"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_INCIDENCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_incidence_cocycle_scan_N128_20260621.json"
)
DEFAULT_FRUSTRATION_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frustration_defect_scan_N128_20260621.json"
)
DEFAULT_ADVERSARIAL_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_adversarial_phase_reference_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frustration_bridge_summary_20260621.json"
)

INCIDENCE_ROW_KEYS = (
    "triad_incidence_rows",
    "incidence_rows",
    "cocycle_rows",
    "rows",
    "items",
    "results",
    "records",
)
FRUSTRATION_ROW_KEYS = (
    "triad_frustration_rows",
    "frustration_rows",
    "defect_rows",
    "rows",
    "items",
    "results",
    "records",
)
ADVERSARIAL_ROW_KEYS = (
    "phase_reference_rows",
    "reference_rows",
    "adversarial_rows",
    "rows",
    "items",
    "results",
    "records",
)
FRAME_KEYS = ("frame", "snapshot_index", "frame_index", "phase_index")
TRIAD_COUNT_KEYS = ("triad_count", "selected_triad_count", "carrier_triad_count")
MODE_COUNT_KEYS = ("mode_count", "selected_mode_count", "carrier_mode_count")
INCIDENCE_DENSITY_KEYS = ("incidence_density", "density", "edge_density")
CYCLE_RANK_KEYS = ("cycle_rank_proxy", "cycle_rank", "cycle_basis_rank", "cycle_density")
SOLVABILITY_KEYS = (
    "exact_lock_proxy",
    "exact_lock_score",
    "solvability_proxy",
    "exact_lock_solvability",
    "lock_proxy",
)
FRUSTRATION_KEYS = (
    "frustration_residual",
    "frustration_residual_mean",
    "frustration_defect",
    "defect",
    "residual",
)
COHERENCE_LOSS_KEYS = ("coherence_loss_proxy", "coherence_loss", "loss_proxy")
TRIAD_WEIGHT_KEYS = ("triad_weight_concentration", "weight_concentration", "triad_concentration")
ADVERSARIAL_GAIN_KEYS = (
    "adversarial_gain",
    "best_minus_zero_constructive_gap",
    "adversarial_lift",
    "max_reference_gain",
    "reference_advantage",
)
BEST_PHASE_KEYS = (
    "best_phase",
    "best_reference_phase",
    "best_reference_phase_offset",
    "argmax_phase",
    "winning_phase",
)
BASELINE_KEYS = (
    "baseline_score",
    "zero_reference_constructive_weight_fraction",
    "random_baseline",
    "uniform_baseline",
)
BEST_SCORE_KEYS = (
    "best_score",
    "best_constructive_weight_fraction",
    "best_constructive_score",
    "winning_score",
)

CONTROL_CARD = {
    "O": "Summarize the triad cocycle/frustration/adversarial telemetry surfaces.",
    "R": (
        "Join the shared frame keys across the three new scans, then emit compact "
        "bridge rows, correlations, and explicit unproved-wall markers."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed on missing inputs, malformed rows, or absent shared keys; telemetry only.",
    "L": (
        "Normalize each scan onto a shared frame key, compute bridge rows and "
        "simple correlations, and expose the live wall as unproved."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this summary.",
    "F": "The finite-dimensional carrier is measured only; the Sacasa bridge remains unproved.",
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
    parser.add_argument("--incidence-json", type=Path, default=DEFAULT_INCIDENCE_JSON)
    parser.add_argument("--frustration-json", type=Path, default=DEFAULT_FRUSTRATION_JSON)
    parser.add_argument("--adversarial-json", type=Path, default=DEFAULT_ADVERSARIAL_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_json_text(payload, pretty) + "\n", encoding="utf-8")


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


def _first_float(row: dict[str, Any], keys: tuple[str, ...]) -> float | None:
    for key in keys:
        value = _coerce_float(row.get(key))
        if value is not None:
            return value
    return None


def _first_int(row: dict[str, Any], keys: tuple[str, ...]) -> int | None:
    for key in keys:
        value = _coerce_int(row.get(key))
        if value is not None:
            return value
    return None


def _extract_rows(payload: dict[str, Any], candidate_keys: tuple[str, ...]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    candidate_containers: list[Any] = [payload]
    for key in ("aggregate", "summary", "frame_aggregate"):
        value = payload.get(key)
        if isinstance(value, dict):
            candidate_containers.append(value)

    index = 0
    while index < len(candidate_containers):
        container = candidate_containers[index]
        index += 1
        if not isinstance(container, dict):
            continue
        if _first_int(container, FRAME_KEYS) is not None:
            rows.append(container)
            continue
        for key in candidate_keys:
            value = container.get(key)
            if isinstance(value, list):
                candidate_containers.extend(value)
            elif isinstance(value, dict):
                candidate_containers.extend(v for v in value.values() if isinstance(v, dict))
        for value in container.values():
            if isinstance(value, dict) and _first_int(value, FRAME_KEYS) is not None:
                rows.append(value)
    return rows


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


def _normalize_by_frame(
    payload: dict[str, Any],
    row_keys: tuple[str, ...],
    warnings: list[str],
) -> dict[int, dict[str, Any]]:
    rows = _extract_rows(payload, row_keys)
    normalized: dict[int, dict[str, Any]] = {}
    for row in rows:
        frame = _first_int(row, FRAME_KEYS)
        if frame is None or frame < 0:
            continue
        normalized[frame] = row
    if not normalized:
        warnings.append("no usable rows found for one source")
    return normalized


def _build_bridge_rows(
    incidence_rows: dict[int, dict[str, Any]],
    frustration_rows: dict[int, dict[str, Any]],
    adversarial_rows: dict[int, dict[str, Any]],
) -> list[dict[str, Any]]:
    shared = sorted(set(incidence_rows) & set(frustration_rows) & set(adversarial_rows))
    bridge_rows: list[dict[str, Any]] = []
    for frame in shared:
        incidence = incidence_rows[frame]
        frustration = frustration_rows[frame]
        adversarial = adversarial_rows[frame]
        bridge_rows.append(
            {
                "frame": frame,
                "triad_count": _first_int(incidence, TRIAD_COUNT_KEYS),
                "mode_count": _first_int(incidence, MODE_COUNT_KEYS),
                "incidence_density": _first_float(incidence, INCIDENCE_DENSITY_KEYS),
                "cycle_rank_proxy": _first_float(incidence, CYCLE_RANK_KEYS),
                "exact_lock_proxy": _first_float(incidence, SOLVABILITY_KEYS),
                "frustration_residual": _first_float(frustration, FRUSTRATION_KEYS),
                "coherence_loss_proxy": _first_float(frustration, COHERENCE_LOSS_KEYS),
                "triad_weight_concentration": _first_float(frustration, TRIAD_WEIGHT_KEYS),
                "adversarial_gain": _first_float(adversarial, ADVERSARIAL_GAIN_KEYS),
                "best_phase": _first_float(adversarial, BEST_PHASE_KEYS),
                "baseline_score": _first_float(adversarial, BASELINE_KEYS),
                "best_score": _first_float(adversarial, BEST_SCORE_KEYS),
                "live_wall_unproved": False,
            }
        )
    return bridge_rows


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    warnings: list[str] = []

    try:
        incidence_payload = _read_json(args.incidence_json)
        frustration_payload = _read_json(args.frustration_json)
        adversarial_payload = _read_json(args.adversarial_json)
    except Exception as exc:  # noqa: BLE001
        payload = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "control_card": CONTROL_CARD,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        _write_json(args.output_json, payload, args.pretty)
        print(_json_text(payload, args.pretty))
        return 1

    incidence_rows = _normalize_by_frame(incidence_payload, INCIDENCE_ROW_KEYS, warnings)
    frustration_rows = _normalize_by_frame(frustration_payload, FRUSTRATION_ROW_KEYS, warnings)
    adversarial_rows = _normalize_by_frame(adversarial_payload, ADVERSARIAL_ROW_KEYS, warnings)

    bridge_rows = _build_bridge_rows(incidence_rows, frustration_rows, adversarial_rows)
    if not bridge_rows:
        errors.append("no shared frame rows across the three telemetry sources")

    cycle_rank = [row["cycle_rank_proxy"] for row in bridge_rows if _coerce_float(row["cycle_rank_proxy"]) is not None]
    frustration_residual = [row["frustration_residual"] for row in bridge_rows if _coerce_float(row["frustration_residual"]) is not None]
    adversarial_gain = [row["adversarial_gain"] for row in bridge_rows if _coerce_float(row["adversarial_gain"]) is not None]
    exact_lock = [row["exact_lock_proxy"] for row in bridge_rows if _coerce_float(row["exact_lock_proxy"]) is not None]
    coherence_loss = [row["coherence_loss_proxy"] for row in bridge_rows if _coerce_float(row["coherence_loss_proxy"]) is not None]

    shared_for_rank_frustration = [
        (float(row["cycle_rank_proxy"]), float(row["frustration_residual"]))
        for row in bridge_rows
        if _coerce_float(row["cycle_rank_proxy"]) is not None
        and _coerce_float(row["frustration_residual"]) is not None
    ]
    shared_for_frustration_gain = [
        (float(row["frustration_residual"]), float(row["adversarial_gain"]))
        for row in bridge_rows
        if _coerce_float(row["frustration_residual"]) is not None
        and _coerce_float(row["adversarial_gain"]) is not None
    ]
    shared_for_lock_loss = [
        (float(row["exact_lock_proxy"]), float(row["coherence_loss_proxy"]))
        for row in bridge_rows
        if _coerce_float(row["exact_lock_proxy"]) is not None
        and _coerce_float(row["coherence_loss_proxy"]) is not None
    ]

    aggregate = {
        "shared_frame_count": len(bridge_rows),
        "coverage_fraction": (
            float(len(bridge_rows))
            / float(max(1, len(set(incidence_rows) | set(frustration_rows) | set(adversarial_rows))))
        ),
        "cycle_rank_proxy_mean": (
            sum(cycle_rank) / len(cycle_rank) if cycle_rank else None
        ),
        "frustration_residual_mean": (
            sum(frustration_residual) / len(frustration_residual)
            if frustration_residual
            else None
        ),
        "adversarial_gain_mean": (
            sum(adversarial_gain) / len(adversarial_gain) if adversarial_gain else None
        ),
        "exact_lock_proxy_mean": (
            sum(exact_lock) / len(exact_lock) if exact_lock else None
        ),
        "coherence_loss_proxy_mean": (
            sum(coherence_loss) / len(coherence_loss) if coherence_loss else None
        ),
        "cycle_rank_vs_frustration_correlation": (
            _pearson(
                [pair[0] for pair in shared_for_rank_frustration],
                [pair[1] for pair in shared_for_rank_frustration],
            )
            if len(shared_for_rank_frustration) >= 2
            else None
        ),
        "frustration_vs_adversarial_gain_correlation": (
            _pearson(
                [pair[0] for pair in shared_for_frustration_gain],
                [pair[1] for pair in shared_for_frustration_gain],
            )
            if len(shared_for_frustration_gain) >= 2
            else None
        ),
        "exact_lock_vs_coherence_loss_correlation": (
            _pearson(
                [pair[0] for pair in shared_for_lock_loss],
                [pair[1] for pair in shared_for_lock_loss],
            )
            if len(shared_for_lock_loss) >= 2
            else None
        ),
        "live_wall_status": "unproved",
        "live_wall_proved": False,
    }

    payload = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "authority": AUTHORITY,
        "inputs": {
            "incidence_json": str(args.incidence_json),
            "frustration_json": str(args.frustration_json),
            "adversarial_json": str(args.adversarial_json),
        },
        "bridge_rows": bridge_rows,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": errors,
    }
    _write_json(args.output_json, payload, args.pretty)
    print(_json_text(payload, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
