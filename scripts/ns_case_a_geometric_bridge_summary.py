#!/usr/bin/env python3
"""Summarize a compact geometric bridge between Case A shell telemetry and boundary-delta1 uniformity.

The bridge is intentionally fail-closed. It joins the shared delta1 thresholds
from the two source scans, records shell-volume shrinkage, boundary-gap
separation, boundary-delta1 minima/quantiles, and a few simple co-movement
metrics. No theorem or Clay promotion claim is inferred.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_case_a_geometric_bridge_summary.py"
CONTRACT = "ns_case_a_geometric_bridge_summary"
SCHEMA_VERSION = "1.0.0"
ROUTE_DECISION = "FAIL_CLOSED_NS_CASE_A_GEOMETRIC_BRIDGE_SUMMARY"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_CASE_A_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_case_a_transition_shell_scan_N128_20260621.json"
)
DEFAULT_BOUNDARY_DELTA1_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_boundary_delta1_uniformity_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_case_a_geometric_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Summarize the Case A shell bridge against boundary-delta1 uniformity telemetry.",
    "R": (
        "Join shared thresholds, shell-volume shrinkage, boundary-gap separation, boundary-delta1 "
        "minima/quantiles, and simple co-movement metrics into one compact ledger."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed on missing inputs, malformed rows, or inconsistent bridge statistics.",
    "L": "Load two scan JSON payloads, normalize threshold rows, align common bins, and emit a compact summary.",
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or promotion claim is inferred by this bridge summary.",
    "F": "Only explicit empirical telemetry and internally consistent threshold joins are allowed.",
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

CASE_A_THRESHOLD_KEYS = (
    "delta1_threshold",
    "threshold",
    "shell_threshold",
    "k0",
)
BOUNDARY_THRESHOLD_KEYS = (
    "delta1_threshold",
    "threshold",
    "gap_threshold",
)
SHELL_VOLUME_KEYS = (
    "shell_volume_shrinkage",
    "shell_volume_fraction",
    "shell_volume",
    "transition_shell_volume",
    "transition_shell_fraction",
    "volume_fraction",
    "volume",
)
BOUNDARY_GAP_KEYS = (
    "boundary_gap_separation",
    "boundary_gap",
    "gap_separation",
    "shell_gap_separation",
    "gap",
    "separation",
)
DELTA1_MIN_KEYS = (
    "delta1_min",
    "boundary_delta1_min",
    "min_delta1",
)
DELTA1_QUANTILE_KEYS = (
    "delta1_quantiles",
    "quantiles",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--case-a-json",
        type=Path,
        default=DEFAULT_CASE_A_JSON,
        help="Case A transition-shell scan JSON.",
    )
    parser.add_argument(
        "--boundary-delta1-json",
        type=Path,
        default=DEFAULT_BOUNDARY_DELTA1_JSON,
        help="Boundary-delta1 uniformity scan JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT_JSON,
        help="Output path for the bridge summary JSON.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output JSON.")
    return parser.parse_args()


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        parsed = int(value)
        return parsed if parsed >= 0 else None
    return None


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    stripped = value.strip()
    return stripped if stripped else None


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level payload must be an object: {path}")
    return payload


def _extract_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    container_dicts: list[dict[str, Any]] = [
        payload,
        payload.get("aggregate") if isinstance(payload.get("aggregate"), dict) else {},
        payload.get("summary") if isinstance(payload.get("summary"), dict) else {},
        payload.get("frame_aggregate") if isinstance(payload.get("frame_aggregate"), dict) else {},
    ]
    candidates: list[Any] = [
        payload,
        payload.get("aggregate"),
        payload.get("summary"),
        payload.get("frame_aggregate"),
    ]
    for container in container_dicts:
        for key in ("rows", "items", "results", "records", "frames", "gap_threshold_rows", "transition_shell_rows", "shell_rows", "threshold_rows", "band_rows", "boundary_band_rows"):
            value = container.get(key)
            if isinstance(value, list):
                candidates.extend(value)
            elif isinstance(value, dict) and key == "gap_threshold_rows":
                candidates.extend(value.values())

    for container in candidates:
        if not isinstance(container, dict):
            continue
        if any(container.get(key) is not None for key in CASE_A_THRESHOLD_KEYS + BOUNDARY_THRESHOLD_KEYS):
            rows.append(container)
            continue
        for value in container.values():
            if isinstance(value, dict) and any(value.get(key) is not None for key in CASE_A_THRESHOLD_KEYS + BOUNDARY_THRESHOLD_KEYS):
                rows.append(value)
    return rows


def _extract_threshold(row: dict[str, Any], keys: tuple[str, ...]) -> float | None:
    for key in keys:
        threshold = _coerce_float(row.get(key))
        if threshold is not None:
            return threshold
    return None


def _normalize_threshold_rows(payload: dict[str, Any], keys: tuple[str, ...]) -> dict[float, dict[str, Any]]:
    normalized: dict[float, dict[str, Any]] = {}
    for row in _extract_rows(payload):
        threshold = _extract_threshold(row, keys)
        if threshold is None:
            continue
        normalized[round(threshold, 12)] = dict(row)
    return normalized


def _first_float(row: dict[str, Any], keys: tuple[str, ...]) -> float | None:
    for key in keys:
        value = _coerce_float(row.get(key))
        if value is not None:
            return value
    return None


def _quantile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    if q <= 0.0:
        return min(values)
    if q >= 1.0:
        return max(values)
    ordered = sorted(values)
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    weight = pos - lo
    return ordered[lo] * (1.0 - weight) + ordered[hi] * weight


def _stats(values: list[float]) -> dict[str, float | int | None]:
    finite = [value for value in values if math.isfinite(value)]
    if not finite:
        return {"count": 0, "min": None, "max": None, "mean": None}
    return {
        "count": len(finite),
        "min": min(finite),
        "max": max(finite),
        "mean": sum(finite) / len(finite),
    }


def _quantiles(values: list[float]) -> dict[str, float | None]:
    finite = [value for value in values if math.isfinite(value)]
    return {
        "p05": _quantile(finite, 0.05),
        "p25": _quantile(finite, 0.25),
        "p50": _quantile(finite, 0.50),
        "p75": _quantile(finite, 0.75),
        "p95": _quantile(finite, 0.95),
    }


def _direction(value: float | None) -> str | None:
    if value is None or not math.isfinite(value):
        return None
    if value > 0.0:
        return "positive"
    if value < 0.0:
        return "negative"
    return "neutral"


def _corr(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) < 2 or len(xs) != len(ys):
        return None
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    num = 0.0
    den_x = 0.0
    den_y = 0.0
    for x, y in zip(xs, ys):
        dx = x - mean_x
        dy = y - mean_y
        num += dx * dy
        den_x += dx * dx
        den_y += dy * dy
    denom = math.sqrt(den_x * den_y)
    return num / denom if denom > 0.0 else None


def _shell_shrinkage(row: dict[str, Any]) -> float | None:
    shrink = _first_float(row, ("shell_volume_shrinkage",))
    if shrink is not None:
        return shrink

    fraction = _first_float(row, ("shell_volume_fraction", "transition_shell_fraction", "volume_fraction"))
    if fraction is not None:
        return 1.0 - fraction

    volume = _first_float(row, ("shell_volume", "transition_shell_volume", "volume"))
    initial = _first_float(row, ("initial_shell_volume", "shell_volume_initial", "reference_shell_volume"))
    if volume is None or initial is None or initial == 0.0:
        return None
    return 1.0 - (volume / initial)


def _boundary_gap(row: dict[str, Any]) -> float | None:
    return _first_float(row, BOUNDARY_GAP_KEYS)


def _delta1_min(row: dict[str, Any]) -> float | None:
    return _first_float(row, DELTA1_MIN_KEYS)


def _delta1_quantiles(row: dict[str, Any]) -> dict[str, float | None]:
    quantiles: dict[str, float | None] = {}
    raw = None
    for key in DELTA1_QUANTILE_KEYS:
        if isinstance(row.get(key), dict):
            raw = row.get(key)
            break
    if isinstance(raw, dict):
        for q_name, aliases in {
            "p05": ("p05", "q05", "0.05", "5%"),
            "p25": ("p25", "q25", "0.25", "25%"),
            "p50": ("p50", "q50", "median", "0.5", "50%"),
            "p75": ("p75", "q75", "0.75", "75%"),
            "p95": ("p95", "q95", "0.95", "95%"),
        }.items():
            quantiles[q_name] = _first_float(raw, aliases)
    else:
        for q_name in ("p05", "p25", "p50", "p75", "p95"):
            quantiles[q_name] = _first_float(row, (f"delta1_{q_name}", f"boundary_delta1_{q_name}", q_name))
    return quantiles


def _normalize_source(
    payload: dict[str, Any],
    source_name: str,
    threshold_keys: tuple[str, ...],
) -> tuple[dict[str, Any], dict[float, dict[str, Any]], list[str]]:
    warnings: list[str] = []
    rows = _normalize_threshold_rows(payload, threshold_keys)
    status = OK_STATUS if rows else ERROR_STATUS
    if not rows:
        warnings.append(f"{source_name}: no usable threshold rows")
    source = {
        "present": True,
        "status": status,
        "path": None,
        "threshold_count": len(rows),
    }
    return source, rows, warnings


def _build_bridge_rows(
    case_a_rows: dict[float, dict[str, Any]],
    boundary_rows: dict[float, dict[str, Any]],
) -> list[dict[str, Any]]:
    thresholds = sorted(set(case_a_rows) & set(boundary_rows))
    bridge_rows: list[dict[str, Any]] = []
    for threshold in thresholds:
        case_a_row = case_a_rows[threshold]
        boundary_row = boundary_rows[threshold]
        shell_shrinkage = _shell_shrinkage(case_a_row)
        boundary_gap = _boundary_gap(case_a_row)
        delta1_min = _delta1_min(case_a_row)
        if delta1_min is None:
            delta1_min = _delta1_min(boundary_row)
        bridge_rows.append(
            {
                "delta1_threshold": threshold,
                "case_a": {
                    "shell_volume_shrinkage": shell_shrinkage,
                    "boundary_gap_separation": boundary_gap,
                    "delta1_min": delta1_min,
                },
                "boundary_delta1": {
                    "boundary_gap_separation": _boundary_gap(boundary_row),
                    "delta1_min": _delta1_min(boundary_row),
                    "delta1_quantiles": _delta1_quantiles(boundary_row),
                },
                "co_movement": {
                    "shell_vs_gap_direction": _direction(shell_shrinkage),
                    "shell_vs_delta1_direction": _direction(delta1_min),
                    "same_direction": None,
                },
            }
        )

    for row in bridge_rows:
        shell = row["case_a"]["shell_volume_shrinkage"]
        gap = row["boundary_delta1"]["boundary_gap_separation"]
        row["co_movement"]["same_direction"] = (
            None if shell is None or gap is None else (_direction(shell) == _direction(gap))
        )
    return bridge_rows


def _direction_summary(values: list[float]) -> str | None:
    if len(values) < 2:
        return None
    diffs = [b - a for a, b in zip(values, values[1:]) if math.isfinite(a) and math.isfinite(b)]
    if not diffs:
        return None
    if all(diff <= 0.0 for diff in diffs):
        return "nonincreasing"
    if all(diff >= 0.0 for diff in diffs):
        return "nondecreasing"
    return "mixed"


def build_summary(case_a_payload: dict[str, Any], boundary_payload: dict[str, Any], case_a_path: Path, boundary_path: Path, output_path: Path) -> dict[str, Any]:
    case_a_source, case_a_rows, case_a_warnings = _normalize_source(case_a_payload, "case_a_transition_shell", CASE_A_THRESHOLD_KEYS)
    boundary_source, boundary_rows, boundary_warnings = _normalize_source(
        boundary_payload,
        "boundary_delta1_uniformity",
        BOUNDARY_THRESHOLD_KEYS,
    )

    shared_thresholds = sorted(set(case_a_rows) & set(boundary_rows))
    bridge_rows = _build_bridge_rows(case_a_rows, boundary_rows)

    shell_values = [row["case_a"]["shell_volume_shrinkage"] for row in bridge_rows if row["case_a"]["shell_volume_shrinkage"] is not None]
    gap_values = [row["boundary_delta1"]["boundary_gap_separation"] for row in bridge_rows if row["boundary_delta1"]["boundary_gap_separation"] is not None]
    delta1_values = [row["boundary_delta1"]["delta1_min"] for row in bridge_rows if row["boundary_delta1"]["delta1_min"] is not None]

    same_direction_count = sum(1 for row in bridge_rows if row["co_movement"]["same_direction"] is True)
    opposite_direction_count = sum(1 for row in bridge_rows if row["co_movement"]["same_direction"] is False)

    shell_diffs = [b - a for a, b in zip(shell_values, shell_values[1:])]
    gap_diffs = [b - a for a, b in zip(gap_values, gap_values[1:])]
    delta1_diffs = [b - a for a, b in zip(delta1_values, delta1_values[1:])]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "status": OK_STATUS if bridge_rows else ERROR_STATUS,
        "inputs": {
            "case_a_json": str(case_a_path),
            "boundary_delta1_json": str(boundary_path),
            "output_json": str(output_path),
        },
        "status_by_source": {
            "case_a_transition_shell": {**case_a_source, "path": str(case_a_path)},
            "boundary_delta1_uniformity": {**boundary_source, "path": str(boundary_path)},
        },
        "case_a_surface": {
            "threshold_count": len(case_a_rows),
            "shell_volume_shrinkage_stats": _stats(shell_values),
            "boundary_gap_separation_stats": _stats(gap_values),
            "delta1_min_stats": _stats(delta1_values),
            "boundary_gap_separation_direction": _direction_summary(gap_values),
        },
        "boundary_delta1_surface": {
            "threshold_count": len(boundary_rows),
            "delta1_min_stats": _stats(delta1_values),
            "delta1_quantiles": {
                "p05": _quantiles(delta1_values)["p05"],
                "p25": _quantiles(delta1_values)["p25"],
                "p50": _quantiles(delta1_values)["p50"],
                "p75": _quantiles(delta1_values)["p75"],
                "p95": _quantiles(delta1_values)["p95"],
            },
        },
        "bridge_rows": bridge_rows,
        "bridge_surface": {
            "threshold_count": len(bridge_rows),
            "shared_threshold_count": len(shared_thresholds),
            "shared_thresholds": shared_thresholds,
            "shell_volume_shrinkage_stats": _stats(shell_values),
            "boundary_gap_separation_stats": _stats(gap_values),
            "boundary_delta1_min_stats": _stats(delta1_values),
            "boundary_delta1_quantiles": {
                "p05": _quantiles(delta1_values)["p05"],
                "p25": _quantiles(delta1_values)["p25"],
                "p50": _quantiles(delta1_values)["p50"],
                "p75": _quantiles(delta1_values)["p75"],
                "p95": _quantiles(delta1_values)["p95"],
            },
            "co_movement": {
                "counted_pairs": len(bridge_rows),
                "same_direction_count": same_direction_count,
                "opposite_direction_count": opposite_direction_count,
                "shell_vs_gap_correlation": _corr(shell_values, gap_values),
                "shell_vs_delta1_correlation": _corr(shell_values, delta1_values),
                "gap_vs_delta1_correlation": _corr(gap_values, delta1_values),
            },
            "monotonicity": {
                "shell_volume_shrinkage": _direction_summary(shell_values),
                "boundary_gap_separation": _direction_summary(gap_values),
                "boundary_delta1_min": _direction_summary(delta1_values),
            },
            "threshold_deltas": {
                "shell_volume_shrinkage": shell_diffs,
                "boundary_gap_separation": gap_diffs,
                "boundary_delta1_min": delta1_diffs,
            },
        },
        "authority": AUTHORITY,
        "errors": [] if bridge_rows else ["no shared thresholds between the two source scans"],
        "warnings": sorted(set(case_a_warnings + boundary_warnings)),
        "changed_files": [str(case_a_path), str(boundary_path), str(output_path)],
        **CONTROL_CARD,
    }
    return summary


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = (
        json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
        if pretty
        else json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)
    ) + "\n"
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = _parse_args()

    try:
        case_a_payload = _read_json(args.case_a_json)
        boundary_payload = _read_json(args.boundary_delta1_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        payload = {
            "contract": CONTRACT,
            "schema_version": SCHEMA_VERSION,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "inputs": {
                "case_a_json": str(args.case_a_json),
                "boundary_delta1_json": str(args.boundary_delta1_json),
                "output_json": str(args.output_json),
            },
            "status_by_source": {
                "case_a_transition_shell": {"present": False, "status": ERROR_STATUS, "path": str(args.case_a_json), "threshold_count": 0},
                "boundary_delta1_uniformity": {"present": False, "status": ERROR_STATUS, "path": str(args.boundary_delta1_json), "threshold_count": 0},
            },
            "case_a_surface": {
                "threshold_count": 0,
                "shell_volume_shrinkage_stats": {"count": 0, "min": None, "max": None, "mean": None},
                "boundary_gap_separation_stats": {"count": 0, "min": None, "max": None, "mean": None},
                "delta1_min_stats": {"count": 0, "min": None, "max": None, "mean": None},
                "boundary_gap_separation_direction": None,
            },
            "boundary_delta1_surface": {
                "threshold_count": 0,
                "delta1_min_stats": {"count": 0, "min": None, "max": None, "mean": None},
                "delta1_quantiles": {"p05": None, "p25": None, "p50": None, "p75": None, "p95": None},
            },
            "bridge_rows": [],
            "bridge_surface": {
                "threshold_count": 0,
                "shared_threshold_count": 0,
                "shared_thresholds": [],
                "shell_volume_shrinkage_stats": {"count": 0, "min": None, "max": None, "mean": None},
                "boundary_gap_separation_stats": {"count": 0, "min": None, "max": None, "mean": None},
                "boundary_delta1_min_stats": {"count": 0, "min": None, "max": None, "mean": None},
                "boundary_delta1_quantiles": {"p05": None, "p25": None, "p50": None, "p75": None, "p95": None},
                "co_movement": {
                    "counted_pairs": 0,
                    "same_direction_count": 0,
                    "opposite_direction_count": 0,
                    "shell_vs_gap_correlation": None,
                    "shell_vs_delta1_correlation": None,
                    "gap_vs_delta1_correlation": None,
                },
                "monotonicity": {
                    "shell_volume_shrinkage": None,
                    "boundary_gap_separation": None,
                    "boundary_delta1_min": None,
                },
                "threshold_deltas": {
                    "shell_volume_shrinkage": [],
                    "boundary_gap_separation": [],
                    "boundary_delta1_min": [],
                },
            },
            "authority": AUTHORITY,
            "errors": [str(exc)],
            "warnings": [],
            "changed_files": [str(args.case_a_json), str(args.boundary_delta1_json), str(args.output_json)],
            **CONTROL_CARD,
        }
        _write_json(args.output_json, payload, args.pretty)
        print(json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None))
        return 1

    summary = build_summary(case_a_payload, boundary_payload, args.case_a_json, args.boundary_delta1_json, args.output_json)
    _write_json(args.output_json, summary, args.pretty)
    print(json.dumps(summary, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if summary["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
