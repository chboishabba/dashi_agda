#!/usr/bin/env python3
"""Summarize triad phase-Laplacian telemetry against basin-rarity telemetry.

This bridge is empirical only. It joins the shared frame keys from the
phase-Laplacian scan and the low-frustration basin scan, then emits a compact
fail-closed summary surface for the Wall 1 / Wall 2 route:

  Wall 1: finite-dimensional entropy / basin barrier
  Wall 2: residence-time exclusion for low-frustration basins
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_entropy_residence_summary.py"
CONTRACT = "ns_triad_entropy_residence_summary"
SCHEMA_VERSION = "1.0.0"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_ENTROPY_RESIDENCE_SUMMARY"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_PHASE_LAPLACIAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_phase_laplacian_scan_N128_20260621.json"
)
DEFAULT_LOW_FRICTION_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_low_frustration_basin_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_entropy_residence_summary_20260621.json"
)

PHASE_ROW_KEYS = (
    "phase_laplacian_rows",
    "triad_phase_laplacian_rows",
    "rows",
    "items",
    "results",
    "records",
)
BASIN_ROW_KEYS = (
    "low_frustration_basin_rows",
    "basin_rows",
    "rows",
    "items",
    "results",
    "records",
)
FRAME_KEYS = ("frame", "snapshot_index", "frame_index", "phase_index")
TRIAD_COUNT_KEYS = ("triad_count", "selected_triad_count", "carrier_triad_count")
MODE_COUNT_KEYS = ("mode_count", "selected_mode_count", "carrier_mode_count")
PHASE_GAP_KEYS = (
    "phase_laplacian_gap",
    "phase_laplacian_gap_proxy",
    "unsigned_laplacian_gap",
    "spectral_gap_proxy",
    "phase_graph_unsigned_laplacian_spectral_gap_proxy",
    "phase_graph_signed_smallest_positive_eigenvalue_proxy",
)
NEGATIVE_RATIO_KEYS = (
    "negative_frame_ratio",
    "negative_mass_ratio",
    "signed_negative_ratio",
    "triad_negative_mass_ratio",
    "phase_graph_negative_mass_ratio",
)
STABILITY_MARGIN_KEYS = (
    "stability_margin",
    "subunit_margin_proxy",
    "operator_margin_proxy",
    "phase_graph_stability_margin_proxy",
    "phase_graph_subunit_proxy",
)
BASIN_OCCUPANCY_KEYS = (
    "low_frustration_basin_fraction",
    "basin_fraction",
    "occupancy_fraction",
    "low_delta_fraction",
    "basin_occupancy_mean",
)
BASIN_RARITY_KEYS = (
    "basin_rarity",
    "negative_log_basin_fraction",
    "negative_log_volume_proxy",
    "rarity_proxy",
    "negative_log_volume_proxy_mean",
)
DELTA_FLOOR_KEYS = (
    "best_frustration_floor",
    "frustration_floor",
    "best_residual_floor",
    "best_reference_floor_proxy",
)

CONTROL_CARD = {
    "O": "Summarize the Wall 1 / Wall 2 triad entropy-residence telemetry surfaces.",
    "R": (
        "Join the shared frame keys across the phase-Laplacian and low-frustration basin scans, "
        "then emit compact bridge rows, correlations, and explicit unproved-wall markers."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed on missing inputs, malformed rows, or absent shared keys; telemetry only.",
    "L": (
        "Normalize each scan onto a shared frame key, compute bridge rows and "
        "simple correlations, and expose the entropy/residence walls as unproved."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this summary.",
    "F": "The finite-dimensional entropy barrier and residence-time exclusion remain unproved.",
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
    parser.add_argument("--phase-laplacian-json", type=Path, default=DEFAULT_PHASE_LAPLACIAN_JSON)
    parser.add_argument("--low-frustration-json", type=Path, default=DEFAULT_LOW_FRICTION_JSON)
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
    by_frame: dict[int, dict[str, Any]] = {}
    for row in _extract_rows(payload, row_keys):
        if not isinstance(row, dict):
            continue
        frame = _first_int(row, FRAME_KEYS)
        if frame is None:
            continue
        if frame in by_frame:
            warnings.append(f"duplicate frame row encountered; keeping first row for frame={frame}")
            continue
        by_frame[frame] = row
    return by_frame


def _route_surface(payload: dict[str, Any], source_name: str) -> dict[str, Any]:
    return {
        "source_name": source_name,
        "present": True,
        "contract": payload.get("contract"),
        "route_decision": payload.get("route_decision"),
        "schema_version": payload.get("schema_version"),
        "status": payload.get("status"),
        "ok": payload.get("status") == OK_STATUS and not payload.get("errors"),
    }


def _mean_or_none(values: list[float]) -> float | None:
    return sum(values) / len(values) if values else None


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    try:
        phase_payload = _read_json(args.phase_laplacian_json)
        basin_payload = _read_json(args.low_frustration_json)
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
        }
        _write_json(args.output_json, payload, args.pretty)
        print(_json_text(payload, args.pretty))
        return 1

    phase_rows = _normalize_by_frame(phase_payload, PHASE_ROW_KEYS, warnings)
    basin_rows = _normalize_by_frame(basin_payload, BASIN_ROW_KEYS, warnings)
    shared = sorted(set(phase_rows) & set(basin_rows))
    if not shared:
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "errors": ["no shared frame keys across phase-Laplacian and basin scans"],
            "warnings": warnings,
            "source_routes": {
                "phase_laplacian_scan": _route_surface(phase_payload, "phase_laplacian_scan"),
                "low_frustration_basin_scan": _route_surface(basin_payload, "low_frustration_basin_scan"),
            },
        }
        _write_json(args.output_json, payload, args.pretty)
        print(_json_text(payload, args.pretty))
        return 1

    bridge_rows: list[dict[str, Any]] = []
    phase_gap_values: list[float] = []
    stability_values: list[float] = []
    occupancy_values: list[float] = []
    rarity_values: list[float] = []
    floor_values: list[float] = []

    for frame in shared:
        phase_row = phase_rows[frame]
        basin_row = basin_rows[frame]
        phase_gap = _first_float(phase_row, PHASE_GAP_KEYS)
        negative_ratio = _first_float(phase_row, NEGATIVE_RATIO_KEYS)
        stability_margin = _first_float(phase_row, STABILITY_MARGIN_KEYS)
        basin_fraction = _first_float(basin_row, BASIN_OCCUPANCY_KEYS)
        basin_rarity = _first_float(basin_row, BASIN_RARITY_KEYS)
        frustration_floor = _first_float(basin_row, DELTA_FLOOR_KEYS)
        row = {
            "frame": frame,
            "triad_count": _first_int(phase_row, TRIAD_COUNT_KEYS) or _first_int(basin_row, TRIAD_COUNT_KEYS),
            "mode_count": _first_int(phase_row, MODE_COUNT_KEYS) or _first_int(basin_row, MODE_COUNT_KEYS),
            "phase_laplacian_gap": phase_gap,
            "negative_frame_ratio": negative_ratio,
            "stability_margin": stability_margin,
            "low_frustration_basin_fraction": basin_fraction,
            "basin_rarity": basin_rarity,
            "best_frustration_floor": frustration_floor,
            "wall1_unproved": False,
            "wall2_unproved": False,
        }
        bridge_rows.append(row)
        if phase_gap is not None:
            phase_gap_values.append(phase_gap)
        if stability_margin is not None:
            stability_values.append(stability_margin)
        if basin_fraction is not None:
            occupancy_values.append(basin_fraction)
        if basin_rarity is not None:
            rarity_values.append(basin_rarity)
        if frustration_floor is not None:
            floor_values.append(frustration_floor)

    phase_gap_vs_rarity_x: list[float] = []
    phase_gap_vs_rarity_y: list[float] = []
    stability_vs_occupancy_x: list[float] = []
    stability_vs_occupancy_y: list[float] = []
    floor_vs_rarity_x: list[float] = []
    floor_vs_rarity_y: list[float] = []

    for row in bridge_rows:
        if row["phase_laplacian_gap"] is not None and row["basin_rarity"] is not None:
            phase_gap_vs_rarity_x.append(float(row["phase_laplacian_gap"]))
            phase_gap_vs_rarity_y.append(float(row["basin_rarity"]))
        if row["stability_margin"] is not None and row["low_frustration_basin_fraction"] is not None:
            stability_vs_occupancy_x.append(float(row["stability_margin"]))
            stability_vs_occupancy_y.append(float(row["low_frustration_basin_fraction"]))
        if row["best_frustration_floor"] is not None and row["basin_rarity"] is not None:
            floor_vs_rarity_x.append(float(row["best_frustration_floor"]))
            floor_vs_rarity_y.append(float(row["basin_rarity"]))

    aggregate = {
        "shared_frame_count": len(shared),
        "coverage_fraction": len(shared) / max(len(set(phase_rows) | set(basin_rows)), 1),
        "phase_laplacian_gap_mean": _mean_or_none(phase_gap_values),
        "stability_margin_mean": _mean_or_none(stability_values),
        "low_frustration_basin_fraction_mean": _mean_or_none(occupancy_values),
        "basin_rarity_mean": _mean_or_none(rarity_values),
        "best_frustration_floor_mean": _mean_or_none(floor_values),
        "phase_gap_vs_rarity_correlation": _pearson(phase_gap_vs_rarity_x, phase_gap_vs_rarity_y),
        "stability_vs_basin_fraction_correlation": _pearson(
            stability_vs_occupancy_x,
            stability_vs_occupancy_y,
        ),
        "frustration_floor_vs_rarity_correlation": _pearson(
            floor_vs_rarity_x,
            floor_vs_rarity_y,
        ),
        "wall1_status": "unproved",
        "wall1_proved": False,
        "wall2_status": "unproved",
        "wall2_proved": False,
    }

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "inputs": {
            "phase_laplacian_json": str(args.phase_laplacian_json),
            "low_frustration_json": str(args.low_frustration_json),
            "output_json": str(args.output_json),
        },
        "source_routes": {
            "phase_laplacian_scan": _route_surface(phase_payload, "phase_laplacian_scan"),
            "low_frustration_basin_scan": _route_surface(basin_payload, "low_frustration_basin_scan"),
        },
        "status": OK_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": aggregate,
        "bridge_rows": bridge_rows,
    }
    _write_json(args.output_json, payload, args.pretty)
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
