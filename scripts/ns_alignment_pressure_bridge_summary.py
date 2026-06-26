#!/usr/bin/env python3
"""Summarize a live bridge across alignment-gap bins, pressure proxies, and Pi_c balance.

The bridge aligns `delta1` threshold rows from the existing alignment gap scan with
optional pressure-eigenframe and compressive-Pi scan surfaces. Missing optional
inputs degrade to an explicit partial status and keep a compact output surface with
explicit warnings/errors.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_alignment_pressure_bridge_summary.py"
CONTRACT = "ns_alignment_pressure_bridge_summary"
SCHEMA_VERSION = "1.0.0"
ROUTE_DECISION = "FAIL_CLOSED_NS_ALIGNMENT_PRESSURE_BRIDGE_SUMMARY"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_STATUS = "missing"
ERROR_STATUS = "error"

DEFAULT_ALIGNMENT_GAP_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_alignment_gap_bin_scan_N128_20260621.json"
)
DEFAULT_PRESSURE_EIGENFRAME_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_pressure_eigenframe_gap_scan_N128_20260621.json"
)
DEFAULT_COMPRESSIVE_PI_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_compressive_pi_decomposition_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_alignment_pressure_bridge_summary_20260621.json"
)

TOLERANCE = 1.0e-12

CONTROL_CARD = {
    "O": "Summarize alignment-gap bridge telemetry with pressure and Pi_c contributions.",
    "R": (
        "Join alignment-gap δ1 bins with optional pressure-correction proxy bins and "
        "optional compressive-vs-extensional Pi_c bins, then emit compact co-movement diagnostics."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "Fail-closed on malformed required inputs; optional missing inputs produce explicit partial "
        "status and warnings, never hidden as success."
    ),
    "L": (
        "Canonicalize source rows by delta1 threshold, align common bins, compute lightweight "
        "correlations/directional co-movement, and report schema-consistency surfaces."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route-promotion claim is inferred by this bridge summary.",
    "F": "Optional sources are partial-by-default, and absent surfaces remain explicit in status/by-source.",
}

SOURCE_ORDER = ("alignment_gap_bin", "pressure_eigenframe", "compressive_pi")

ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_STATUS, ERROR_STATUS}
ALLOWED_ALIGNMENT_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

# Canonical alias sets for optional streams; keep broad for heterogeneous scan outputs.
PRESSURE_COMPRESSIVE_ALIASES = (
    "pressure_correction_compressive",
    "pressure_compressive",
    "pressure_proxy_compressive",
    "pressure_correction_proxy_compressive",
    "compressive_pressure_proxy",
    "compressive_pressure_correction",
    "compressive_proxy",
)
PRESSURE_EXTENSIONAL_ALIASES = (
    "pressure_correction_extensional",
    "pressure_extensional",
    "pressure_proxy_extensional",
    "pressure_correction_proxy_extensional",
    "extensional_pressure_proxy",
    "extensional_pressure_correction",
    "extensional_proxy",
)
PRESSURE_BALANCE_ALIASES = (
    "pressure_proxy_balance",
    "pressure_balance",
    "pressure_correction_balance",
    "pressure_balance_proxy",
)

PI_COMPRESSIVE_ALIASES = (
    "pi_c_compressive",
    "compressive_pi_c",
    "pi_c_compressive_contribution",
    "compressive_pi_contribution",
)
PI_EXTENSIONAL_ALIASES = (
    "pi_c_extensional",
    "extensional_pi_c",
    "pi_c_extensional_contribution",
    "extensional_pi_c_contribution",
)
PI_BALANCE_ALIASES = (
    "pi_c_balance",
    "pi_balance",
    "pi_c_compressive_extensional_balance",
    "compressive_extensional_pi_c_balance",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--alignment-gap-json",
        type=Path,
        default=DEFAULT_ALIGNMENT_GAP_JSON,
        help="Alignment-gap scan JSON (required).",
    )
    parser.add_argument(
        "--pressure-eigenframe-json",
        type=Path,
        default=DEFAULT_PRESSURE_EIGENFRAME_JSON,
        help="Optional pressure-eigenframe scan JSON.",
    )
    parser.add_argument(
        "--compressive-pi-json",
        type=Path,
        default=DEFAULT_COMPRESSIVE_PI_JSON,
        help="Optional compressive-Pi scan JSON.",
    )
    parser.add_argument("--no-pressure-eigenframe", action="store_true", help="Skip optional pressure stream.")
    parser.add_argument("--no-compressive-pi", action="store_true", help="Skip optional Pi_c stream.")
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT_JSON,
        help="Output path for summary JSON.",
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
    if not math.isfinite(parsed):
        return None
    return parsed


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value) if int(value) >= 0 else None
    if isinstance(value, str):
        try:
            parsed = float(value.strip())
        except ValueError:
            return None
        if math.isfinite(parsed) and parsed.is_integer():
            return int(parsed) if int(parsed) >= 0 else None
    return None


def _coerce_status(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    normalized = value.strip().lower()
    return normalized if normalized in ALLOWED_STATUSES else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _to_bin_key(value: float) -> float:
    return round(float(value), 12)


def _read_json(
    path: Path,
    warnings: list[str],
    errors: list[str],
    optional: bool = False,
) -> dict[str, Any] | None:
    if not path.exists():
        if optional:
            warnings.append(f"missing optional input file: {path}")
            return None
        errors.append(f"missing required input file: {path}")
        return None

    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{path}: {exc}")
        return None

    if not isinstance(payload, dict):
        errors.append(f"{path}: top-level payload must be an object")
        return None
    return payload


def _extract_rows(payload: dict[str, Any], candidate_keys: tuple[str, ...]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    candidate_containers: list[Any] = [
        payload,
        payload.get("aggregate"),
        payload.get("frame_aggregate"),
        payload.get("summary"),
    ]
    for key in ("frames", "items", "records", "results"):
        value = payload.get(key)
        if isinstance(value, list):
            candidate_containers.extend(value)

    for container in candidate_containers:
        if not isinstance(container, dict):
            continue
        for key in candidate_keys:
            value = container.get(key)
            if isinstance(value, list):
                for row in value:
                    if isinstance(row, dict):
                        rows.append(row)
            elif isinstance(value, dict) and key == "gap_threshold_rows":
                # Support alternate packaging of map-like rows.
                nested_values = [nested for nested in value.values() if isinstance(nested, dict)]
                rows.extend(nested_values)

    if rows:
        return rows

    # Fallback: top-level values that are row-like.
    for value in payload.values():
        if not isinstance(value, dict):
            continue
        for row in value.values():
            if isinstance(row, dict):
                maybe_threshold = row.get("delta1_threshold")
                if maybe_threshold is not None:
                    rows.append(row)
    return rows


def _extract_threshold_rows(
    payload: dict[str, Any],
    row_keys: tuple[str, ...],
    warnings: list[str],
) -> dict[float, dict[str, Any]]:
    collected: dict[float, dict[str, Any]] = {}
    row_candidates = _extract_rows(payload, row_keys)
    for row in row_candidates:
        if not isinstance(row, dict):
            continue
        threshold = _coerce_float(row.get("delta1_threshold"))
        if threshold is None:
            threshold = _coerce_float(row.get("delta1"))
        if threshold is None:
            threshold = _coerce_float(row.get("threshold"))
        if threshold is None:
            continue
        collected[_to_bin_key(threshold)] = dict(row)

    if not collected:
        warnings.append(f"no parseable delta1-threshold rows found in keys: {', '.join(row_keys)}")
    return collected


def _row_status_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    status_counts: dict[str, int] = {status: 0 for status in ALLOWED_STATUSES}
    for row in rows:
        status = _coerce_status(row.get("status")) or OK_STATUS
        status_counts[status] = status_counts.get(status, 0) + 1
    status_counts = {key: value for key, value in status_counts.items() if value}
    return status_counts


def _normalize_gap_rows(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> tuple[dict[str, Any], bool]:
    source: dict[str, Any] = {
        "present": True,
        "status": OK_STATUS,
        "path": None,
        "bin_count": 0,
        "rows": [],
    }

    raw_rows = _extract_threshold_rows(
        payload,
        ("gap_threshold_rows", "delta1_bins", "rows", "items", "results", "records"),
        warnings,
    )
    if not raw_rows:
        source["status"] = ERROR_STATUS
        source["bin_count"] = 0
        errors.append("alignment_gap_bin: no usable delta1 rows")
        return source, False

    normalized: list[dict[str, Any]] = []
    status_counts = _row_status_counts(list(raw_rows.values()))
    for threshold_key in sorted(raw_rows):
        row = raw_rows[threshold_key]
        align_e1 = _coerce_float(row.get("align_e1_fraction"))
        align_e3 = _coerce_float(row.get("align_e3_fraction"))
        align_tie = _coerce_float(row.get("align_tie_fraction"))
        align_success = _coerce_float(
            row.get("align_success_fraction")
        ) or _coerce_float(row.get("align_rule_success_fraction")) or (
            (align_e1 + align_e3) if align_e1 is not None and align_e3 is not None else None
        )
        align_success = align_success if align_success is not None else None

        if align_e1 is not None and align_e3 is not None and align_tie is not None:
            total = align_e1 + align_e3 + align_tie
            if abs(total - 1.0) > 2e-3:
                warnings.append(f"alignment_gap_bin: threshold {threshold_key} fraction sum={total:.6g} != 1")

        if align_success is None:
            warnings.append(f"alignment_gap_bin: threshold {threshold_key} missing align_success_fraction")

        normalized.append(
            {
                "delta1_threshold": float(threshold_key),
                "align_success_fraction": align_success,
                "align_e1_fraction": align_e1,
                "align_e3_fraction": align_e3,
                "align_tie_fraction": align_tie,
                "status": row.get("status", OK_STATUS),
            }
        )

    source["bin_count"] = len(normalized)
    source["rows"] = normalized
    source["status"] = OK_STATUS if source["bin_count"] > 0 and ERROR_STATUS not in status_counts else ERROR_STATUS
    if status_counts.get(MISSING_STATUS, 0) and source["status"] != ERROR_STATUS:
        source["status"] = PARTIAL_STATUS
    return source, source["status"] == OK_STATUS or source["status"] == PARTIAL_STATUS


def _collect_proxy(
    row: dict[str, Any],
    compressive_aliases: tuple[str, ...],
    extensional_aliases: tuple[str, ...],
    balance_aliases: tuple[str, ...],
) -> tuple[float | None, float | None, float | None]:
    compressive = None
    for name in compressive_aliases:
        if _coerce_float(row.get(name)) is not None:
            compressive = _coerce_float(row.get(name))
            break

    extensional = None
    for name in extensional_aliases:
        if _coerce_float(row.get(name)) is not None:
            extensional = _coerce_float(row.get(name))
            break

    balance = None
    for name in balance_aliases:
        value = _coerce_float(row.get(name))
        if value is not None:
            balance = value
            break

    if balance is None and compressive is not None and extensional is not None:
        denom = abs(compressive) + abs(extensional)
        if denom > 0.0:
            balance = (compressive - extensional) / denom
        elif abs(compressive) > 0.0 or abs(extensional) > 0.0:
            balance = float("inf") if compressive >= extensional else float("-inf")

    if balance is None:
        return compressive, extensional, None
    return compressive, extensional, balance


def _compute_balance(compressive: float | None, extensional: float | None) -> float | None:
    if compressive is None or extensional is None:
        return None
    denom = abs(compressive) + abs(extensional)
    if denom > 0.0:
        return (compressive - extensional) / denom
    if abs(compressive) > 0.0 or abs(extensional) > 0.0:
        return float("inf") if compressive >= extensional else float("-inf")
    return 0.0


def _pressure_proxy_from_row(row: dict[str, Any]) -> tuple[float | None, float | None, float | None]:
    p12 = _coerce_float(row.get("p12_scaled_mean"))
    p13 = _coerce_float(row.get("p13_scaled_mean"))
    p23 = _coerce_float(row.get("p23_scaled_mean"))
    if p12 is None and p13 is None and p23 is None:
        return None, None, None
    compressive = None
    if p12 is not None or p13 is not None:
        compressive = (p12 or 0.0) + (p13 or 0.0)
    extensional = p23
    return compressive, extensional, _compute_balance(compressive, extensional)


def _pi_proxy_from_payload(payload: dict[str, Any]) -> tuple[float | None, float | None, float | None]:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        return None, None, None
    pi1 = _coerce_float(aggregate.get("global_pi1_sum"))
    pi2 = _coerce_float(aggregate.get("global_pi2_sum"))
    pi3 = _coerce_float(aggregate.get("global_pi3_sum"))
    if pi1 is None and pi2 is None and pi3 is None:
        return None, None, None
    compressive = max(-(pi1 or 0.0), 0.0)
    extensional = max(pi2 or 0.0, 0.0) + max(pi3 or 0.0, 0.0)
    return compressive, extensional, _compute_balance(compressive, extensional)


def _normalize_optional_rows(
    payload: dict[str, Any],
    source_name: str,
    compressive_aliases: tuple[str, ...],
    extensional_aliases: tuple[str, ...],
    balance_aliases: tuple[str, ...],
    warnings: list[str],
    errors: list[str],
) -> tuple[dict[str, Any], bool]:
    source: dict[str, Any] = {
        "present": True,
        "status": OK_STATUS,
        "path": None,
        "bin_count": 0,
        "rows": [],
    }

    raw_rows = _extract_threshold_rows(
        payload,
        (
            "delta1_bins",
            "gap_threshold_rows",
            "rows",
            "items",
            "results",
            "records",
            "bin_rows",
        ),
        warnings,
    )
    if not raw_rows:
        source["status"] = MISSING_STATUS
        source["bin_count"] = 0
        warnings.append(f"{source_name}: no parseable delta1-threshold rows")
        return source, True

    normalized: list[dict[str, Any]] = []
    for threshold_key in sorted(raw_rows):
        row = raw_rows[threshold_key]
        compressive, extensional, balance = _collect_proxy(
            row,
            compressive_aliases,
            extensional_aliases,
            balance_aliases,
        )
        if compressive is None and extensional is None and balance is None:
            status = _coerce_status(row.get("status")) or OK_STATUS
            normalized.append(
                {
                    "delta1_threshold": float(threshold_key),
                    "compressive": None,
                    "extensional": None,
                    "balance": None,
                    "status": status,
                    "unusable": True,
                }
            )
            continue

        normalized.append(
            {
                "delta1_threshold": float(threshold_key),
                "compressive": compressive,
                "extensional": extensional,
                "balance": balance,
                "status": _coerce_status(row.get("status")) or OK_STATUS,
            }
        )

    usable_rows = [row for row in normalized if any(row.get(name) is not None for name in ("compressive", "extensional", "balance"))]
    source["bin_count"] = len(usable_rows)
    source["rows"] = usable_rows
    source["status"] = (
        PARTIAL_STATUS
        if source["bin_count"] == 0
        else OK_STATUS
    )
    if source["bin_count"] == 0:
        warnings.append(f"{source_name}: no usable proxy columns from recognized aliases at any delta1 threshold")
    return source, source["status"] in (OK_STATUS, PARTIAL_STATUS)


def _normalize_pressure_source(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> tuple[dict[str, Any], bool]:
    source, ok = _normalize_optional_rows(
        payload,
        "pressure_eigenframe",
        PRESSURE_COMPRESSIVE_ALIASES,
        PRESSURE_EXTENSIONAL_ALIASES,
        PRESSURE_BALANCE_ALIASES,
        warnings,
        errors,
    )
    if source["bin_count"] > 0:
        return source, ok

    raw_rows = _extract_threshold_rows(
        payload,
        ("gap_threshold_rows", "delta1_bins", "rows", "items", "results", "records", "bin_rows"),
        warnings=[],
    )
    derived_rows: list[dict[str, Any]] = []
    for threshold_key in sorted(raw_rows):
        compressive, extensional, balance = _pressure_proxy_from_row(raw_rows[threshold_key])
        if compressive is None and extensional is None and balance is None:
            continue
        derived_rows.append(
            {
                "delta1_threshold": float(threshold_key),
                "compressive": compressive,
                "extensional": extensional,
                "balance": balance,
                "status": _coerce_status(raw_rows[threshold_key].get("status")) or OK_STATUS,
            }
        )

    if derived_rows:
        source["rows"] = derived_rows
        source["bin_count"] = len(derived_rows)
        source["status"] = OK_STATUS
    return source, ok


def _normalize_pi_source(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> tuple[dict[str, Any], bool]:
    source, ok = _normalize_optional_rows(
        payload,
        "compressive_pi",
        PI_COMPRESSIVE_ALIASES,
        PI_EXTENSIONAL_ALIASES,
        PI_BALANCE_ALIASES,
        warnings,
        errors,
    )
    if source["bin_count"] > 0:
        return source, ok

    compressive, extensional, balance = _pi_proxy_from_payload(payload)
    if compressive is not None or extensional is not None or balance is not None:
        source["rows"] = [
            {
                "delta1_threshold": 0.0,
                "compressive": compressive,
                "extensional": extensional,
                "balance": balance,
                "status": _coerce_status(payload.get("status")) or OK_STATUS,
            }
        ]
        source["bin_count"] = 1
        source["status"] = OK_STATUS
    return source, ok


def _direction(balance: float | None) -> str | None:
    if balance is None or not math.isfinite(balance):
        return None
    if balance > 0.0:
        return "compressive"
    if balance < 0.0:
        return "extensional"
    return "neutral"


def _alignment_direction(value: float | None) -> str | None:
    if value is None:
        return None
    if value > 0.5:
        return "success"
    if value < 0.5:
        return "misalign"
    return "neutral"


def _fractional_correlation(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) < 2 or len(xs) != len(ys):
        return None
    n = len(xs)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    numerator = 0.0
    denominator_x = 0.0
    denominator_y = 0.0
    for x, y in zip(xs, ys):
        dx = x - mean_x
        dy = y - mean_y
        numerator += dx * dy
        denominator_x += dx * dx
        denominator_y += dy * dy
    denom = math.sqrt(denominator_x * denominator_y)
    return numerator / denom if denom > 0.0 else None


def _summarize_series(values: list[float | None]) -> dict[str, float | None]:
    finite = [value for value in values if _coerce_float(value) is not None]
    if not finite:
        return {"count": 0, "min": None, "max": None, "mean": None}
    return {
        "count": len(finite),
        "min": min(finite),
        "max": max(finite),
        "mean": sum(finite) / len(finite),
    }


def _is_monotonic(values: list[float | None], tolerance: float = 0.0) -> bool | None:
    finite = [value for value in values if _coerce_float(value) is not None]
    if len(finite) < 2:
        return None
    return all((finite[i + 1] + tolerance) >= finite[i] for i in range(len(finite) - 1))


def _build_bridge_rows(
    gap_rows: list[dict[str, Any]],
    pressure_rows: list[dict[str, Any]],
    pi_rows: list[dict[str, Any]],
    warnings: list[str],
) -> tuple[list[dict[str, Any]], dict[str, Any], int]:
    gap_map = {}
    for row in gap_rows:
        threshold = _coerce_float(row.get("delta1_threshold"))
        if threshold is not None:
            gap_map[_to_bin_key(threshold)] = row

    pressure_map = {}
    for row in pressure_rows:
        threshold = _coerce_float(row.get("delta1_threshold"))
        if threshold is not None:
            pressure_map[_to_bin_key(threshold)] = row

    pi_map = {}
    for row in pi_rows:
        threshold = _coerce_float(row.get("delta1_threshold"))
        if threshold is not None:
            pi_map[_to_bin_key(threshold)] = row

    thresholds = sorted(set(gap_map) | set(pressure_map) | set(pi_map))
    bridge_rows: list[dict[str, Any]] = []

    pressure_balance_values: list[float] = []
    pi_balance_values: list[float] = []
    gap_success_values: list[float] = []

    co_movement_counts = {
        "pressure_alignment_same_direction": 0,
        "pressure_alignment_opposite_direction": 0,
        "pi_alignment_same_direction": 0,
        "pi_alignment_opposite_direction": 0,
        "pressure_pi_same_direction": 0,
        "pressure_pi_opposite_direction": 0,
        "counted_pairs": 0,
    }
    for threshold in thresholds:
        gap = gap_map.get(threshold)
        pressure = pressure_map.get(threshold)
        pi = pi_map.get(threshold)

        gap_success = _coerce_float(gap.get("align_success_fraction")) if isinstance(gap, dict) else None
        pressure_balance = _coerce_float(pressure.get("balance")) if isinstance(pressure, dict) else None
        pi_balance = _coerce_float(pi.get("balance")) if isinstance(pi, dict) else None

        row: dict[str, Any] = {"delta1_threshold": float(threshold)}
        if gap is not None:
            row["alignment_gap"] = {
                "align_success_fraction": gap.get("align_success_fraction"),
                "align_e1_fraction": gap.get("align_e1_fraction"),
                "align_e3_fraction": gap.get("align_e3_fraction"),
                "align_tie_fraction": gap.get("align_tie_fraction"),
            }

        if pressure is not None and pressure.get("compressive") is not None or pressure is not None and pressure.get("extensional") is not None or pressure is not None and pressure.get("balance") is not None:
            row["pressure_proxy"] = {
                "compressive_proxy": pressure.get("compressive"),
                "extensional_proxy": pressure.get("extensional"),
                "balance": pressure_balance,
            }

        if pi is not None and pi.get("compressive") is not None or pi is not None and pi.get("extensional") is not None or pi is not None and pi.get("balance") is not None:
            row["compressive_pi"] = {
                "compressive_pi_c": pi.get("compressive"),
                "extensional_pi_c": pi.get("extensional"),
                "balance": pi_balance,
            }

        if gap_success is not None:
            if pressure_balance is not None:
                pressure_success_direction = _alignment_direction(gap_success) == _direction(pressure_balance)
                pressure_balance_values.append(pressure_balance)
                if pressure_success_direction:
                    co_movement_counts["pressure_alignment_same_direction"] += 1
                else:
                    co_movement_counts["pressure_alignment_opposite_direction"] += 1
            if pi_balance is not None:
                pi_success_direction = _alignment_direction(gap_success) == _direction(pi_balance)
                pi_balance_values.append(pi_balance)
                if pi_success_direction:
                    co_movement_counts["pi_alignment_same_direction"] += 1
                else:
                    co_movement_counts["pi_alignment_opposite_direction"] += 1
            gap_success_values.append(gap_success)

        if pressure_balance is not None and pi_balance is not None:
            pressure_dir = _direction(pressure_balance)
            pi_dir = _direction(pi_balance)
            if pressure_dir is not None and pi_dir is not None:
                co_movement_counts["counted_pairs"] += 1
                if pressure_dir == pi_dir:
                    co_movement_counts["pressure_pi_same_direction"] += 1
                else:
                    co_movement_counts["pressure_pi_opposite_direction"] += 1
                row["co_movement"] = {
                    "pressure_direction": pressure_dir,
                    "pi_c_direction": pi_dir,
                    "all_directional_same": pressure_dir == pi_dir,
                }
            else:
                row["co_movement"] = {
                    "pressure_direction": pressure_dir,
                    "pi_c_direction": pi_dir,
                    "all_directional_same": None,
                }

        bridge_rows.append(row)

    bridge_surface = {
        "threshold_count": len(thresholds),
        "shared_threshold_count": {
            "gap_pressure": sum(1 for threshold in thresholds if threshold in gap_map and threshold in pressure_map),
            "gap_pi": sum(1 for threshold in thresholds if threshold in gap_map and threshold in pi_map),
            "all_three": sum(
                1
                for threshold in thresholds
                if threshold in gap_map and threshold in pressure_map and threshold in pi_map
            ),
        },
        "correlations": {
            "gap_vs_pressure_balance": _fractional_correlation(gap_success_values, pressure_balance_values),
            "gap_vs_pi_c_balance": _fractional_correlation(gap_success_values, pi_balance_values),
        },
        "co_movement": co_movement_counts,
        "monotonicity": {
            "alignment_success": _is_monotonic([row.get("alignment_gap", {}).get("align_success_fraction") for row in bridge_rows], 0.0),
            "pressure_balance": _is_monotonic([row.get("pressure_proxy", {}).get("balance") for row in bridge_rows], 0.0),
            "pi_c_balance": _is_monotonic([row.get("compressive_pi", {}).get("balance") for row in bridge_rows], 0.0),
        },
        "pressure_proxy_bins_missing_from_gap": sorted(
            [float(threshold) for threshold in sorted(set(pressure_map) - set(gap_map))]
        ),
        "compressive_pi_bins_missing_from_gap": sorted(
            [float(threshold) for threshold in sorted(set(pi_map) - set(gap_map))]
        ),
    }

    return bridge_rows, bridge_surface, len(thresholds)


def _authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }


def _build_summary(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    warnings: list[str] = []
    errors: list[str] = []
    status = OK_STATUS

    alignment_payload = _read_json(args.alignment_gap_json, warnings, errors, optional=False)
    alignment_source = {
        "present": bool(alignment_payload is not None),
        "status": MISSING_STATUS,
        "path": str(args.alignment_gap_json),
        "bin_count": 0,
        "rows": [],
    }
    gap_rows: list[dict[str, Any]] = []
    if alignment_payload is None:
        status = ERROR_STATUS
        alignment_source["status"] = ERROR_STATUS
    else:
        alignment_source_data, ok = _normalize_gap_rows(alignment_payload, warnings, errors)
        alignment_source = {
            "present": True,
            "status": alignment_source_data["status"],
            "path": str(args.alignment_gap_json),
            "bin_count": int(alignment_source_data["bin_count"]),
            "rows": alignment_source_data["rows"],
        }
        gap_rows = alignment_source_data["rows"] if isinstance(alignment_source_data.get("rows"), list) else []
        if not ok:
            status = ERROR_STATUS

    if status == ERROR_STATUS:
        payload: dict[str, Any] = {
            "contract": CONTRACT,
            "schema_version": SCHEMA_VERSION,
            "route_decision": ROUTE_DECISION,
            "status": status,
            "authority": _authority(),
            "status_by_source": {
                "alignment_gap_bin": {
                    "present": alignment_source["present"],
                    "status": alignment_source["status"],
                    "path": alignment_source["path"],
                    "bin_count": alignment_source["bin_count"],
                },
                "pressure_eigenframe": {
                    "present": False,
                    "status": MISSING_STATUS,
                    "path": str(args.pressure_eigenframe_json),
                    "bin_count": 0,
                },
                "compressive_pi": {
                    "present": False,
                    "status": MISSING_STATUS,
                    "path": str(args.compressive_pi_json),
                    "bin_count": 0,
                },
            },
            "inputs": {
                "alignment_gap_json": str(args.alignment_gap_json),
                "pressure_eigenframe_json": str(args.pressure_eigenframe_json),
                "compressive_pi_json": str(args.compressive_pi_json),
            },
            "bridge_rows": [],
            "bridge_surface": {
                "threshold_count": 0,
                "shared_threshold_count": {
                    "gap_pressure": 0,
                    "gap_pi": 0,
                    "all_three": 0,
                },
                "correlations": {
                    "gap_vs_pressure_balance": None,
                    "gap_vs_pi_c_balance": None,
                },
                "co_movement": {
                    "pressure_alignment_same_direction": 0,
                    "pressure_alignment_opposite_direction": 0,
                    "pi_alignment_same_direction": 0,
                    "pi_alignment_opposite_direction": 0,
                    "pressure_pi_same_direction": 0,
                    "pressure_pi_opposite_direction": 0,
                    "counted_pairs": 0,
                },
                "monotonicity": {
                    "alignment_success": None,
                    "pressure_balance": None,
                    "pi_c_balance": None,
                },
                "pressure_proxy_bins_missing_from_gap": [],
                "compressive_pi_bins_missing_from_gap": [],
            },
            "errors": errors,
            "warnings": warnings,
            "changed_files": [str(args.output_json)],
            **CONTROL_CARD,
        }
        return payload, 1

    pressure_source_data: dict[str, Any]
    if args.no_pressure_eigenframe:
        pressure_source_data = {
            "present": False,
            "status": MISSING_STATUS,
            "path": str(args.pressure_eigenframe_json),
            "bin_count": 0,
            "rows": [],
        }
        warnings.append("pressure_eigenframe source disabled via --no-pressure-eigenframe")
    else:
        pressure_payload = _read_json(args.pressure_eigenframe_json, warnings, errors, optional=True)
        if pressure_payload is None:
            pressure_source_data = {
                "present": False,
                "status": MISSING_STATUS,
                "path": str(args.pressure_eigenframe_json),
                "bin_count": 0,
                "rows": [],
            }
        else:
            pressure_source_data, pressure_ok = _normalize_pressure_source(pressure_payload, warnings, errors)
            pressure_source_data["present"] = True
            pressure_source_data["path"] = str(args.pressure_eigenframe_json)
            if not pressure_ok:
                status = PARTIAL_STATUS

    if pressure_source_data["status"] == ERROR_STATUS:
        status = PARTIAL_STATUS

    if args.no_compressive_pi:
        pi_source_data = {
            "present": False,
            "status": MISSING_STATUS,
            "path": str(args.compressive_pi_json),
            "bin_count": 0,
            "rows": [],
        }
        warnings.append("compressive_pi source disabled via --no-compressive-pi")
    else:
        pi_payload = _read_json(args.compressive_pi_json, warnings, errors, optional=True)
        if pi_payload is None:
            pi_source_data = {
                "present": False,
                "status": MISSING_STATUS,
                "path": str(args.compressive_pi_json),
                "bin_count": 0,
                "rows": [],
            }
        else:
            pi_source_data, pi_ok = _normalize_pi_source(pi_payload, warnings, errors)
            pi_source_data["present"] = True
            pi_source_data["path"] = str(args.compressive_pi_json)
            if not pi_ok:
                status = PARTIAL_STATUS

    if pi_source_data["status"] == ERROR_STATUS:
        status = PARTIAL_STATUS

    if alignment_source["status"] != OK_STATUS:
        status = ERROR_STATUS
    if status != ERROR_STATUS and alignment_source["status"] == OK_STATUS and status != PARTIAL_STATUS:
        status = OK_STATUS

    if alignment_source["status"] == PARTIAL_STATUS and status == OK_STATUS:
        status = PARTIAL_STATUS

    pressure_rows = pressure_source_data.get("rows", [])
    if not isinstance(pressure_rows, list):
        pressure_rows = []
    pi_rows = pi_source_data.get("rows", [])
    if not isinstance(pi_rows, list):
        pi_rows = []

    bridge_rows, bridge_surface, threshold_count = _build_bridge_rows(
        gap_rows=gap_rows,
        pressure_rows=pressure_rows,
        pi_rows=pi_rows,
        warnings=warnings,
    )

    if alignment_source["bin_count"] == 0:
        status = ERROR_STATUS
        errors.append("alignment source produced no usable bins")

    if threshold_count == 0 and status != ERROR_STATUS:
        status = PARTIAL_STATUS
        errors.append("no bins from joint alignment/optional streams to synthesize")

    gap_success_values = [row["alignment_gap"]["align_success_fraction"] for row in bridge_rows if row.get("alignment_gap", {}).get("align_success_fraction") is not None]
    bridge_surface["alignment_gap_success_stats"] = _summarize_series(gap_success_values)
    bridge_surface["pressure_proxy_balance_stats"] = _summarize_series(
        [row.get("pressure_proxy", {}).get("balance") for row in bridge_rows]
    )
    bridge_surface["compressive_pi_balance_stats"] = _summarize_series(
        [row.get("compressive_pi", {}).get("balance") for row in bridge_rows]
    )

    if alignment_source["status"] != ERROR_STATUS and status != ERROR_STATUS and threshold_count > 0:
        if alignment_source["bin_count"] > 0 and status != PARTIAL_STATUS:
            status = OK_STATUS

    if not any(source["present"] for source in (pressure_source_data, pi_source_data)):
        status = PARTIAL_STATUS
        warnings.append("both optional sources missing; bridge carries only alignment rows")

    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "status": status,
        "authority": _authority(),
        "status_by_source": {
            "alignment_gap_bin": {
                "present": alignment_source["present"],
                "status": alignment_source["status"],
                "path": alignment_source["path"],
                "bin_count": alignment_source["bin_count"],
            },
            "pressure_eigenframe": {
                "present": pressure_source_data["present"],
                "status": pressure_source_data["status"],
                "path": pressure_source_data["path"],
                "bin_count": pressure_source_data["bin_count"],
            },
            "compressive_pi": {
                "present": pi_source_data["present"],
                "status": pi_source_data["status"],
                "path": pi_source_data["path"],
                "bin_count": pi_source_data["bin_count"],
            },
        },
        "inputs": {
            "alignment_gap_json": str(args.alignment_gap_json),
            "pressure_eigenframe_json": str(args.pressure_eigenframe_json),
            "compressive_pi_json": str(args.compressive_pi_json),
        },
        "bridge_rows": bridge_rows,
        "bridge_surface": bridge_surface,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "changed_files": sorted(
            {str(args.alignment_gap_json), str(args.pressure_eigenframe_json), str(args.compressive_pi_json), str(args.output_json)}
        ),
        **CONTROL_CARD,
    }

    # Align final status with source statuses and emitted diagnostics.
    if not alignment_source["present"] or alignment_source["status"] == ERROR_STATUS:
        status = ERROR_STATUS
    elif any(source_status in {ERROR_STATUS} for source_status in (pressure_source_data["status"], pi_source_data["status"])):
        status = PARTIAL_STATUS
    elif status not in (OK_STATUS, PARTIAL_STATUS, ERROR_STATUS):
        status = ERROR_STATUS
    payload["status"] = status

    return payload, 0 if status == OK_STATUS else 1


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    if pretty:
        text = json.dumps(payload, sort_keys=True, indent=2, allow_nan=False) + "\n"
    else:
        text = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = _parse_args()
    payload, code = _build_summary(args)
    _write_json(args.output_json, payload, args.pretty)
    print(json.dumps({"contract": payload["contract"], "status": payload["status"]}, sort_keys=True))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
