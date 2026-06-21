#!/usr/bin/env python3
"""Summarize orbit-phase/coherence telemetry against non-Sobolev telemetry.

This bridge is telemetry only. It joins the shared orbit-phase keys from the
new orbit/coherence scan and the non-Sobolev scan, then emits a compact
fail-closed summary surface with explicit source routes, correlations, and an
unproved live-wall marker.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_sacasa_kiriukhin_bridge_summary.py"
CONTRACT = "ns_sacasa_kiriukhin_bridge_summary"
SCHEMA_VERSION = "1.0.0"
ROUTE_DECISION = "FAIL_CLOSED_NS_SACASA_KIRIUKHIN_BRIDGE_SUMMARY"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_ORBIT_PHASE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_orbit_phase_coherence_scan_N128_20260621.json"
)
DEFAULT_NON_SOBOLEV_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_non_sobolev_telemetry_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_sacasa_kiriukhin_bridge_summary_20260621.json"
)

ORBIT_ROW_KEYS = (
    "orbit_phase_rows",
    "phase_rows",
    "orbit_rows",
    "rows",
    "items",
    "results",
    "records",
)
NON_SOBOLEV_ROW_KEYS = (
    "non_sobolev_rows",
    "sobolev_rows",
    "rows",
    "items",
    "results",
    "records",
)
PHASE_KEY_ALIASES = (
    "orbit_phase",
    "phase",
    "phase_index",
    "orbit_phase_index",
    "snapshot_index",
    "frame",
)
ORBIT_COHERENCE_ALIASES = (
    "orbit_coherence",
    "coherence",
    "phase_coherence",
    "coherence_mean",
    "phase_lock",
    "phase_lock_fraction",
)
ORBIT_EXTRA_ALIASES = (
    "orbit_phase_strength",
    "phase_strength",
    "phase_amplitude",
    "amplitude",
    "phase_alignment",
)
NON_SOBOLEV_MARGIN_ALIASES = (
    "non_sobolev_margin",
    "sobolev_deficit",
    "sobolev_gap",
    "non_sobolev_gap",
    "hminus_gap",
    "wall_slack",
    "wall_margin",
)
NON_SOBOLEV_SCORE_ALIASES = (
    "non_sobolev_score",
    "sobolev_score",
    "wall_score",
    "criticality",
)

CONTROL_CARD = {
    "O": "Summarize orbit-phase/coherence telemetry against non-Sobolev telemetry.",
    "R": (
        "Join the shared orbit-phase keys across the orbit/coherence scan and the non-Sobolev "
        "scan, then emit compact correlations, aggregates, and route metadata."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed on missing inputs, malformed rows, or absent shared keys; no hidden promotion path exists.",
    "L": (
        "Normalize both scans onto a shared phase key, compute bridge rows and simple correlations, "
        "and surface explicit source routes plus the live-wall status."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or proof claim is inferred from this telemetry bridge.",
    "F": "The live wall is recorded as unproved; absent or unusable inputs remain explicit errors.",
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
    parser.add_argument(
        "--orbit-phase-json",
        type=Path,
        default=DEFAULT_ORBIT_PHASE_JSON,
        help="Orbit-phase/coherence scan JSON.",
    )
    parser.add_argument(
        "--non-sobolev-json",
        type=Path,
        default=DEFAULT_NON_SOBOLEV_JSON,
        help="Non-Sobolev telemetry scan JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT_JSON,
        help="Output path for the bridge summary JSON.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output JSON.")
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
    value = value.strip()
    return value if value else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _first_float(row: dict[str, Any], keys: tuple[str, ...]) -> float | None:
    for key in keys:
        value = _coerce_float(row.get(key))
        if value is not None:
            return value
    return None


def _first_nonempty_str(row: dict[str, Any], keys: tuple[str, ...]) -> str | None:
    for key in keys:
        value = _coerce_nonempty_str(row.get(key))
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
        phase_key = _first_float(container, PHASE_KEY_ALIASES)
        if phase_key is not None:
            rows.append(container)
            continue
        for key in candidate_keys:
            value = container.get(key)
            if isinstance(value, list):
                candidate_containers.extend(value)
            elif isinstance(value, dict):
                candidate_containers.extend(v for v in value.values() if isinstance(v, dict))
        for value in container.values():
            if isinstance(value, dict) and _first_float(value, PHASE_KEY_ALIASES) is not None:
                rows.append(value)
    return rows


def _normalize_source(
    payload: dict[str, Any],
    source_name: str,
    row_keys: tuple[str, ...],
    metric_keys: tuple[str, ...],
    extra_keys: tuple[str, ...],
    warnings: list[str],
    errors: list[str],
) -> dict[str, Any]:
    source: dict[str, Any] = {
        "present": True,
        "status": OK_STATUS,
        "path": None,
        "row_count": 0,
        "usable_row_count": 0,
        "rows": [],
    }

    raw_rows = _extract_rows(payload, row_keys)
    source["row_count"] = len(raw_rows)
    if not raw_rows:
        source["status"] = ERROR_STATUS
        errors.append(f"{source_name}: no parseable rows")
        return source

    normalized: list[dict[str, Any]] = []
    for row in raw_rows:
        phase_key = _first_float(row, PHASE_KEY_ALIASES)
        if phase_key is None:
            continue
        coherence = _first_float(row, metric_keys)
        extra = _first_float(row, extra_keys)
        label = _first_nonempty_str(row, ("orbit_phase_label", "phase_label", "label", "name"))
        normalized.append(
            {
                "phase_key": round(float(phase_key), 12),
                "phase_key_raw": phase_key,
                "phase_label": label,
                "coherence": coherence,
                "extra": extra,
                "status": _coerce_nonempty_str(row.get("status")) or OK_STATUS,
            }
        )

    source["usable_row_count"] = len(normalized)
    source["rows"] = normalized
    if not normalized:
        source["status"] = ERROR_STATUS
        errors.append(f"{source_name}: rows did not contain a parseable phase key")
        return source

    if source["usable_row_count"] == 0:
        source["status"] = ERROR_STATUS
        errors.append(f"{source_name}: no usable phase rows")
    else:
        source["status"] = OK_STATUS
    if any(row["coherence"] is None for row in normalized):
        warnings.append(f"{source_name}: some rows are missing coherence metrics")
    return source


def _normalize_non_sobolev_source(
    payload: dict[str, Any],
    warnings: list[str],
    errors: list[str],
) -> dict[str, Any]:
    return _normalize_source(
        payload,
        "non_sobolev_scan",
        NON_SOBOLEV_ROW_KEYS,
        NON_SOBOLEV_MARGIN_ALIASES,
        NON_SOBOLEV_SCORE_ALIASES,
        warnings,
        errors,
    )


def _normalize_orbit_source(
    payload: dict[str, Any],
    warnings: list[str],
    errors: list[str],
) -> dict[str, Any]:
    return _normalize_source(
        payload,
        "orbit_phase_scan",
        ORBIT_ROW_KEYS,
        ORBIT_COHERENCE_ALIASES,
        ORBIT_EXTRA_ALIASES,
        warnings,
        errors,
    )


def _pearson(xs: list[float], ys: list[float]) -> float | None:
    pairs = [
        (x, y)
        for x, y in zip(xs, ys, strict=True)
        if x is not None and y is not None and math.isfinite(x) and math.isfinite(y)
    ]
    if len(pairs) < 2:
        return None
    x_vals = [x for x, _ in pairs]
    y_vals = [y for _, y in pairs]
    x_mean = sum(x_vals) / len(x_vals)
    y_mean = sum(y_vals) / len(y_vals)
    numerator = sum((x - x_mean) * (y - y_mean) for x, y in pairs)
    x_var = sum((x - x_mean) ** 2 for x in x_vals)
    y_var = sum((y - y_mean) ** 2 for y in y_vals)
    if x_var <= 0.0 or y_var <= 0.0:
        return None
    return numerator / math.sqrt(x_var * y_var)


def _finite_series(values: list[float | None]) -> list[float]:
    return [value for value in values if value is not None and math.isfinite(value)]


def _stats(values: list[float | None]) -> dict[str, float | int | None]:
    finite = _finite_series(values)
    if not finite:
        return {"count": 0, "min": None, "max": None, "mean": None}
    return {
        "count": len(finite),
        "min": min(finite),
        "max": max(finite),
        "mean": sum(finite) / len(finite),
    }


def _build_bridge_rows(
    orbit_source: dict[str, Any],
    non_sobolev_source: dict[str, Any],
    warnings: list[str],
) -> tuple[list[dict[str, Any]], dict[str, Any], int]:
    orbit_rows = orbit_source.get("rows", [])
    non_rows = non_sobolev_source.get("rows", [])
    orbit_map = {
        row["phase_key"]: row
        for row in orbit_rows
        if isinstance(row, dict) and _coerce_float(row.get("phase_key")) is not None
    }
    non_map = {
        row["phase_key"]: row
        for row in non_rows
        if isinstance(row, dict) and _coerce_float(row.get("phase_key")) is not None
    }
    shared_keys = sorted(set(orbit_map) & set(non_map))
    if not shared_keys:
        return [], {
            "orbit_phase_row_count": len(orbit_map),
            "non_sobolev_row_count": len(non_map),
            "shared_key_count": 0,
            "orbit_only_key_count": len(set(orbit_map) - set(non_map)),
            "non_sobolev_only_key_count": len(set(non_map) - set(orbit_map)),
            "bridge_row_count": 0,
            "coverage_fraction": 0.0,
            "correlations": {
                "orbit_phase_vs_coherence": None,
                "orbit_phase_vs_non_sobolev": None,
                "coherence_vs_non_sobolev": None,
            },
            "coherence": {"orbit": _stats([]), "non_sobolev": _stats([])},
            "live_wall_proved": False,
            "live_wall_status": "unproved",
        }, 0

    bridge_rows: list[dict[str, Any]] = []
    orbit_phase_series: list[float] = []
    coherence_series: list[float | None] = []
    non_sobolev_series: list[float | None] = []
    extra_series: list[float | None] = []

    for phase_key in shared_keys:
        orbit_row = orbit_map[phase_key]
        non_row = non_map[phase_key]
        coherence = _coerce_float(orbit_row.get("coherence"))
        non_sobolev = _coerce_float(non_row.get("coherence"))
        extra = _coerce_float(orbit_row.get("extra"))
        row = {
            "orbit_phase": float(phase_key),
            "orbit_phase_raw": orbit_row.get("phase_key_raw"),
            "phase_label": orbit_row.get("phase_label") or non_row.get("phase_label"),
            "orbit_coherence": coherence,
            "orbit_extra": extra,
            "non_sobolev_metric": non_sobolev,
            "live_wall_unproved": False,
        }
        bridge_rows.append(row)
        orbit_phase_series.append(float(phase_key))
        coherence_series.append(coherence)
        non_sobolev_series.append(non_sobolev)
        extra_series.append(extra)

    coverage_fraction = len(shared_keys) / float(max(len(orbit_map), len(non_map), 1))
    surface = {
        "orbit_phase_row_count": len(orbit_map),
        "non_sobolev_row_count": len(non_map),
        "shared_key_count": len(shared_keys),
        "orbit_only_key_count": len(set(orbit_map) - set(non_map)),
        "non_sobolev_only_key_count": len(set(non_map) - set(orbit_map)),
        "bridge_row_count": len(bridge_rows),
        "coverage_fraction": coverage_fraction,
        "correlations": {
            "orbit_phase_vs_coherence": _pearson(orbit_phase_series, coherence_series),
            "orbit_phase_vs_non_sobolev": _pearson(orbit_phase_series, non_sobolev_series),
            "coherence_vs_non_sobolev": _pearson(coherence_series, non_sobolev_series),
        },
        "coherence": {
            "orbit": _stats(coherence_series),
            "non_sobolev": _stats(non_sobolev_series),
            "orbit_extra": _stats(extra_series),
        },
        "live_wall_proved": False,
        "live_wall_status": "unproved",
    }
    if coverage_fraction <= 0.0:
        warnings.append("shared_key coverage_fraction is zero")
    return bridge_rows, surface, len(shared_keys)


def main() -> int:
    args = _parse_args()
    result: dict[str, Any] = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "inputs": {
            "orbit_phase_json": str(args.orbit_phase_json),
            "non_sobolev_json": str(args.non_sobolev_json),
            "output_json": str(args.output_json),
        },
        "source_routes": {},
    }
    errors: list[str] = []
    warnings: list[str] = []
    try:
        orbit_payload = _read_json(args.orbit_phase_json)
        non_payload = _read_json(args.non_sobolev_json)
    except Exception as exc:  # noqa: BLE001
        result["status"] = ERROR_STATUS
        result["errors"] = [str(exc)]
        result["warnings"] = []
        _write_json(args.output_json, result, args.pretty)
        print(_json_text(result, args.pretty))
        return 1

    orbit_source = _normalize_orbit_source(orbit_payload, warnings, errors)
    non_source = _normalize_non_sobolev_source(non_payload, warnings, errors)
    orbit_source["path"] = str(args.orbit_phase_json)
    non_source["path"] = str(args.non_sobolev_json)
    result["source_routes"] = {
        "orbit_phase_scan": orbit_source,
        "non_sobolev_scan": non_source,
    }

    bridge_rows, bridge_surface, shared_key_count = _build_bridge_rows(orbit_source, non_source, warnings)
    if shared_key_count == 0:
        errors.append("no shared orbit-phase keys across orbit_phase_scan and non_sobolev_scan")

    result["bridge_rows"] = bridge_rows
    result["bridge_surface"] = bridge_surface
    result["live_wall_proved"] = False
    result["live_wall_status"] = "unproved"

    if orbit_source.get("status") != OK_STATUS:
        errors.append("orbit_phase_scan did not normalize cleanly")
    if non_source.get("status") != OK_STATUS:
        errors.append("non_sobolev_scan did not normalize cleanly")

    status = OK_STATUS if not errors else ERROR_STATUS
    result["status"] = status
    result["errors"] = errors
    result["warnings"] = warnings

    _write_json(args.output_json, result, args.pretty)
    print(_json_text(result, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
