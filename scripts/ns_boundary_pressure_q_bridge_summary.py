#!/usr/bin/env python3
"""Summarize the bridge between boundary pressure-gate telemetry and existing NS scans."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_boundary_pressure_q_bridge_summary.py"
CONTRACT = "ns_boundary_pressure_q_bridge_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_PRESSURE_Q_BRIDGE_SUMMARY"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"

DEFAULT_BOUNDARY_PRESSURE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_pressure_gate_scan_N128_20260621.json"
)
DEFAULT_BOUNDARY_DELTA1_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_boundary_delta1_uniformity_scan_N128_20260621.json"
)
DEFAULT_PRESSURE_GAP_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_pressure_eigenframe_gap_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_pressure_q_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Bridge boundary pressure-gate telemetry with delta1 and pressure-gap summaries.",
    "R": (
        "Join shared delta1 thresholds across the boundary pressure scan, boundary-delta1 "
        "scan, and pressure-eigenframe gap scan, then emit compact co-movement metrics."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed on malformed required sources; optional missing sources degrade to partial, never silent success.",
    "L": "Extract canonical threshold rows, intersect thresholds, compute bridge rows and compact correlations.",
    "P": ROUTE_DECISION,
    "G": "Bridge is empirical and non-promoting.",
    "F": "Any missing or inconsistent threshold surface remains explicit in status/source metadata.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--boundary-pressure-json", type=Path, default=DEFAULT_BOUNDARY_PRESSURE_JSON)
    parser.add_argument("--boundary-delta1-json", type=Path, default=DEFAULT_BOUNDARY_DELTA1_JSON)
    parser.add_argument("--pressure-gap-json", type=Path, default=DEFAULT_PRESSURE_GAP_JSON)
    parser.add_argument("--no-boundary-delta1", action="store_true")
    parser.add_argument("--no-pressure-gap", action="store_true")
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


def _finite_float(value: Any) -> float | None:
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _to_key(value: float) -> float:
    return float(f"{float(value):.12g}")


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


def _boundary_rows(payload: dict[str, Any]) -> dict[float, dict[str, Any]]:
    rows = payload.get("aggregate", {}).get("boundary_threshold_rows", [])
    result: dict[float, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        threshold = _finite_float(row.get("delta1_threshold"))
        if threshold is None:
            continue
        result[_to_key(threshold)] = row
    return result


def _delta1_rows(payload: dict[str, Any]) -> dict[float, dict[str, Any]]:
    rows = payload.get("aggregate", {}).get("gap_threshold_rows", [])
    result: dict[float, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        threshold = _finite_float(row.get("delta1_threshold"))
        if threshold is None:
            continue
        result[_to_key(threshold)] = row
    return result


def _pressure_gap_rows(payload: dict[str, Any]) -> dict[float, dict[str, Any]]:
    rows = payload.get("aggregate", {}).get("gap_threshold_rows", [])
    result: dict[float, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        threshold = _finite_float(row.get("delta1_threshold"))
        if threshold is None:
            continue
        result[_to_key(threshold)] = row
    return result


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    errors: list[str] = []

    try:
        boundary_payload = _read_json(args.boundary_pressure_json)
    except Exception as exc:  # noqa: BLE001
        result = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "authority": {
                "candidate_only": True,
                "empirical_non_promoting": True,
                "truth_authority": False,
                "theorem_authority": False,
                "clay_authority": False,
                "runtime_authority": False,
                "promoted": False,
            },
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(result, args.pretty))
        return 1

    boundary_rows = _boundary_rows(boundary_payload)
    if not boundary_rows:
        errors.append("boundary pressure scan has no aggregate boundary_threshold_rows")

    delta1_rows: dict[float, dict[str, Any]] = {}
    pressure_gap_rows: dict[float, dict[str, Any]] = {}
    status_by_source: dict[str, dict[str, Any]] = {
        "boundary_pressure": {
            "path": str(args.boundary_pressure_json),
            "present": True,
            "status": boundary_payload.get("status"),
            "bin_count": len(boundary_rows),
        }
    }

    if not args.no_boundary_delta1:
        try:
            delta1_payload = _read_json(args.boundary_delta1_json)
            delta1_rows = _delta1_rows(delta1_payload)
            status_by_source["boundary_delta1"] = {
                "path": str(args.boundary_delta1_json),
                "present": True,
                "status": delta1_payload.get("status"),
                "bin_count": len(delta1_rows),
            }
        except Exception as exc:  # noqa: BLE001
            warnings.append(f"boundary_delta1 unavailable: {exc}")
            status_by_source["boundary_delta1"] = {
                "path": str(args.boundary_delta1_json),
                "present": False,
                "status": "missing",
                "bin_count": 0,
            }
    else:
        status_by_source["boundary_delta1"] = {
            "path": str(args.boundary_delta1_json),
            "present": False,
            "status": "missing",
            "bin_count": 0,
        }

    if not args.no_pressure_gap:
        try:
            pressure_gap_payload = _read_json(args.pressure_gap_json)
            pressure_gap_rows = _pressure_gap_rows(pressure_gap_payload)
            status_by_source["pressure_gap"] = {
                "path": str(args.pressure_gap_json),
                "present": True,
                "status": pressure_gap_payload.get("status"),
                "bin_count": len(pressure_gap_rows),
            }
        except Exception as exc:  # noqa: BLE001
            warnings.append(f"pressure_gap unavailable: {exc}")
            status_by_source["pressure_gap"] = {
                "path": str(args.pressure_gap_json),
                "present": False,
                "status": "missing",
                "bin_count": 0,
            }
    else:
        status_by_source["pressure_gap"] = {
            "path": str(args.pressure_gap_json),
            "present": False,
            "status": "missing",
            "bin_count": 0,
        }

    shared = set(boundary_rows)
    if delta1_rows:
        shared &= set(delta1_rows)
    if pressure_gap_rows:
        shared &= set(pressure_gap_rows)
    shared_thresholds = sorted(shared)
    if not shared_thresholds:
        shared_thresholds = sorted(boundary_rows)

    bridge_rows: list[dict[str, Any]] = []
    q_neg_series: list[float] = []
    p11_neg_series: list[float] = []
    q_gap_series: list[float] = []
    q_delta1_series: list[float] = []
    delta1_min_series: list[float] = []
    for threshold in shared_thresholds:
        boundary_row = boundary_rows[threshold]
        delta1_row = delta1_rows.get(threshold)
        gap_row = pressure_gap_rows.get(threshold)
        row = {
            "delta1_threshold": float(threshold),
            "boundary_q_negative_fraction": float(boundary_row.get("q_negative_fraction", 0.0)),
            "boundary_p11_negative_fraction": float(boundary_row.get("p11_negative_fraction", 0.0)),
            "boundary_q_mean": float(boundary_row.get("q_mean", 0.0)),
            "boundary_p11_mean": float(boundary_row.get("p11_mean", 0.0)),
            "boundary_omega2_dominant_fraction": float(boundary_row.get("omega2_dominant_fraction", 0.0)),
            "boundary_delta1_min": delta1_row.get("delta1_min") if delta1_row is not None else None,
            "boundary_gap_separation": delta1_row.get("boundary_gap_separation") if delta1_row is not None else None,
            "pressure_gap_p12_scaled_mean": gap_row.get("p12_scaled_mean") if gap_row is not None else None,
            "pressure_gap_p13_scaled_mean": gap_row.get("p13_scaled_mean") if gap_row is not None else None,
            "pressure_gap_p23_scaled_mean": gap_row.get("p23_scaled_mean") if gap_row is not None else None,
        }
        bridge_rows.append(row)
        q_neg = _finite_float(row["boundary_q_negative_fraction"])
        p11_neg = _finite_float(row["boundary_p11_negative_fraction"])
        q_gap = _finite_float(row["pressure_gap_p12_scaled_mean"])
        delta1_min = _finite_float(row["boundary_delta1_min"])
        q_mean = _finite_float(row["boundary_q_mean"])
        if q_neg is not None:
            q_neg_series.append(q_neg)
        if p11_neg is not None:
            p11_neg_series.append(p11_neg)
        if q_gap is not None:
            q_gap_series.append(q_gap)
        if delta1_min is not None and q_mean is not None:
            q_delta1_series.append(abs(q_mean))
            delta1_min_series.append(delta1_min)

    status = OK_STATUS
    if errors:
        status = ERROR_STATUS
    elif warnings:
        status = PARTIAL_STATUS

    result = {
        **CONTROL_CARD,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "status": status,
        "inputs": {
            "boundary_pressure_json": str(args.boundary_pressure_json),
            "boundary_delta1_json": str(args.boundary_delta1_json),
            "pressure_gap_json": str(args.pressure_gap_json),
        },
        "status_by_source": status_by_source,
        "shared_thresholds": [float(x) for x in shared_thresholds],
        "bridge_rows": bridge_rows,
        "aggregate": {
            "threshold_count": len(shared_thresholds),
            "q_negative_fraction_mean": float(sum(q_neg_series) / len(q_neg_series)) if q_neg_series else 0.0,
            "p11_negative_fraction_mean": float(sum(p11_neg_series) / len(p11_neg_series)) if p11_neg_series else 0.0,
            "q_vs_p11_negative_fraction_correlation": _pearson(q_neg_series, p11_neg_series),
            "q_vs_pressure_gap_p12_scaled_mean_correlation": _pearson(
                [float(r["boundary_q_negative_fraction"]) for r in bridge_rows if _finite_float(r["pressure_gap_p12_scaled_mean"]) is not None],
                [float(r["pressure_gap_p12_scaled_mean"]) for r in bridge_rows if _finite_float(r["pressure_gap_p12_scaled_mean"]) is not None],
            ),
            "abs_q_mean_vs_boundary_delta1_min_correlation": _pearson(q_delta1_series, delta1_min_series),
        },
        "warnings": warnings,
        "errors": errors,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(result, args.pretty))
    return 0 if status != ERROR_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
