#!/usr/bin/env python3
"""Bridge tube-morphology telemetry with boundary pressure/helicity surfaces."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_tube_pressure_helicity_bridge_summary.py"
CONTRACT = "ns_tube_pressure_helicity_bridge_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TUBE_PRESSURE_HELICITY_BRIDGE_SUMMARY"
SCHEMA_VERSION = "1.0.0"
OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"

DEFAULT_MORPHOLOGY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_tube_morphology_scan_N128_20260621.json"
)
DEFAULT_BOUNDARY_HELICITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_helicity_q_scan_N128_20260621.json"
)
DEFAULT_BOUNDARY_PRESSURE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_pressure_gate_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_tube_pressure_helicity_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Bridge new tube-morphology telemetry with boundary pressure and helicity surfaces.",
    "R": (
        "Join morphology, boundary helicity/Q, and boundary pressure scans by frame, "
        "then emit compact co-movement rows and correlations."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed on malformed required sources; missing rows degrade explicitly to partial.",
    "L": "Extract canonical per-frame rows, join on frame/snapshot pairs, compute bridge rows, and summarize correlations.",
    "P": ROUTE_DECISION,
    "G": "Empirical/non-promoting bridge only.",
    "F": "Bridge co-movement remains telemetry rather than proof.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--morphology-json", type=Path, default=DEFAULT_MORPHOLOGY_JSON)
    parser.add_argument("--boundary-helicity-json", type=Path, default=DEFAULT_BOUNDARY_HELICITY_JSON)
    parser.add_argument("--boundary-pressure-json", type=Path, default=DEFAULT_BOUNDARY_PRESSURE_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: payload must be object")
    return payload


def _pearson(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    x_mean = sum(xs) / len(xs)
    y_mean = sum(ys) / len(ys)
    num = sum((x - x_mean) * (y - y_mean) for x, y in zip(xs, ys, strict=True))
    x_var = sum((x - x_mean) ** 2 for x in xs)
    y_var = sum((y - y_mean) ** 2 for y in ys)
    if x_var <= 0.0 or y_var <= 0.0:
        return None
    return float(num / math.sqrt(x_var * y_var))


def _best_morphology_row(row: dict[str, Any]) -> dict[str, Any] | None:
    rows = row.get("quantile_rows", [])
    if not isinstance(rows, list) or not rows:
        return None
    candidates = [entry for entry in rows if isinstance(entry, dict)]
    if not candidates:
        return None
    return max(candidates, key=lambda entry: float(entry.get("carrier_quantile", 0.0)))


def _best_threshold_row(row: dict[str, Any], field: str = "threshold_rows") -> dict[str, Any] | None:
    rows = row.get(field, [])
    if not isinstance(rows, list) or not rows:
        return None
    candidates = [entry for entry in rows if isinstance(entry, dict)]
    if not candidates:
        return None
    return max(candidates, key=lambda entry: float(entry.get("delta1_threshold", 0.0)))


def _frame_map(payload: dict[str, Any]) -> dict[tuple[int, int], dict[str, Any]]:
    frame_rows = payload.get("frame_rows", [])
    result: dict[tuple[int, int], dict[str, Any]] = {}
    for row in frame_rows:
        if not isinstance(row, dict):
            continue
        if row.get("status") != OK_STATUS:
            continue
        frame = row.get("frame")
        snapshot = row.get("snapshot_index")
        if not isinstance(frame, int) or not isinstance(snapshot, int):
            continue
        result[(frame, snapshot)] = row
    return result


def main() -> int:
    args = _parse_args()
    result: dict[str, Any] = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
        "sources": {},
    }
    errors: list[str] = []
    warnings: list[str] = []
    try:
        morphology = _read_json(args.morphology_json)
        boundary_helicity = _read_json(args.boundary_helicity_json)
        boundary_pressure = _read_json(args.boundary_pressure_json)
    except Exception as exc:  # noqa: BLE001
        result["status"] = ERROR_STATUS
        result["errors"] = [str(exc)]
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(result, args.pretty))
        return 1

    result["sources"] = {
        "morphology": {"path": str(args.morphology_json), "status": morphology.get("status")},
        "boundary_helicity": {"path": str(args.boundary_helicity_json), "status": boundary_helicity.get("status")},
        "boundary_pressure": {"path": str(args.boundary_pressure_json), "status": boundary_pressure.get("status")},
    }

    morph_by_frame = _frame_map(morphology)
    helicity_by_frame = _frame_map(boundary_helicity)
    pressure_by_frame = _frame_map(boundary_pressure)

    shared_keys = sorted(set(morph_by_frame) & set(helicity_by_frame) & set(pressure_by_frame))
    if not shared_keys:
        errors.append("no shared OK frame rows across morphology/helicity/pressure sources")

    bridge_rows: list[dict[str, Any]] = []
    tube_series: list[float] = []
    depleting_series: list[float] = []
    q_negative_series: list[float] = []
    p11_negative_series: list[float] = []
    abs_q_series: list[float] = []
    abs_helicity_series: list[float] = []

    for frame, snapshot in shared_keys:
        morph_row = morph_by_frame[(frame, snapshot)]
        helicity_row = helicity_by_frame[(frame, snapshot)]
        pressure_row = pressure_by_frame[(frame, snapshot)]

        best_morph = _best_morphology_row(morph_row)
        best_helicity = _best_threshold_row(helicity_row)
        best_pressure = _best_threshold_row(pressure_row)
        if best_morph is None or best_helicity is None or best_pressure is None:
            warnings.append(f"shared frame ({frame},{snapshot}) missing canonical subordinate row")
            continue

        row = {
            "frame": int(frame),
            "snapshot_index": int(snapshot),
            "carrier_quantile": float(best_morph.get("carrier_quantile", 0.0)),
            "delta1_threshold": float(best_helicity.get("delta1_threshold", 0.0)),
            "tube_like_fraction": float(best_morph.get("tube_like_fraction", 0.0)),
            "sheet_like_fraction": float(best_morph.get("sheet_like_fraction", 0.0)),
            "blob_like_fraction": float(best_morph.get("blob_like_fraction", 0.0)),
            "tube_axis_alignment_mean": float(best_morph.get("tube_axis_alignment_mean", 0.0)),
            "q_negative_fraction": float(best_pressure.get("q_negative_fraction", 0.0)),
            "p11_negative_fraction": float(best_pressure.get("p11_negative_fraction", 0.0)),
            "depleting_pair_fraction": float(best_helicity.get("depleting_pair_fraction", 0.0)),
            "helicity_positive_fraction": float(best_helicity.get("helicity_positive_fraction", 0.0)),
            "q_helicity_correlation": best_helicity.get("q_helicity_correlation"),
            "abs_q_mean": float(best_helicity.get("abs_q_mean", 0.0)),
            "abs_helicity_mean": float(best_helicity.get("abs_helicity_mean", 0.0)),
        }
        bridge_rows.append(row)
        tube_series.append(row["tube_like_fraction"])
        depleting_series.append(row["depleting_pair_fraction"])
        q_negative_series.append(row["q_negative_fraction"])
        p11_negative_series.append(row["p11_negative_fraction"])
        abs_q_series.append(row["abs_q_mean"])
        abs_helicity_series.append(row["abs_helicity_mean"])

    result["bridge_rows"] = bridge_rows
    result["aggregate"] = {
        "shared_frame_count": len(bridge_rows),
        "tube_vs_depleting_pair_correlation": _pearson(tube_series, depleting_series),
        "tube_vs_q_negative_correlation": _pearson(tube_series, q_negative_series),
        "tube_vs_p11_negative_correlation": _pearson(tube_series, p11_negative_series),
        "q_negative_vs_depleting_pair_correlation": _pearson(q_negative_series, depleting_series),
        "abs_q_vs_abs_helicity_correlation": _pearson(abs_q_series, abs_helicity_series),
    }
    result["status"] = OK_STATUS if not errors else ERROR_STATUS
    if warnings and not errors:
        result["status"] = PARTIAL_STATUS
    if warnings:
        result["warnings"] = warnings
    if errors:
        result["errors"] = errors
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(result, args.pretty))
    return 0 if result["status"] in {OK_STATUS, PARTIAL_STATUS} else 1


if __name__ == "__main__":
    raise SystemExit(main())
