#!/usr/bin/env python3
"""Validate ns_triad_entropy_residence_summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_entropy_residence_summary.py"
CONTRACT = "check_ns_triad_entropy_residence_summary"
SOURCE_CONTRACT = "ns_triad_entropy_residence_summary"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_ENTROPY_RESIDENCE_SUMMARY"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_ENTROPY_RESIDENCE_SUMMARY_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"
PARTIAL_STATUS = "partial"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}
EXPECTED_SOURCE_NAMES = ("phase_laplacian_scan", "low_frustration_basin_scan")

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_entropy_residence_summary_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_entropy_residence_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate the Wall 1 / Wall 2 triad entropy-residence summary output.",
    "R": "Check schema, source routes, bridge rows, aggregate metrics, and explicit unproved-wall markers.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed entropy-residence bridge summaries.",
    "L": "Load the summary JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field, authority drift, or proved-wall claim is a hard error.",
}

SOURCE_CONTROL_CARD = {
    "O": "Summarize the Wall 1 / Wall 2 triad entropy-residence telemetry surfaces.",
    "R": (
        "Join the shared frame keys across the phase-Laplacian and low-frustration basin scans, "
        "then emit compact bridge rows, correlations, and explicit unproved-wall markers."
    ),
    "C": "scripts/ns_triad_entropy_residence_summary.py",
    "S": "Fail-closed on missing inputs, malformed rows, or absent shared keys; telemetry only.",
    "L": (
        "Normalize each scan onto a shared frame key, compute bridge rows and "
        "simple correlations, and expose the entropy/residence walls as unproved."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this summary.",
    "F": "The finite-dimensional entropy barrier and residence-time exclusion remain unproved.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_json", nargs="?", type=Path)
    parser.add_argument("--source-json", type=Path, dest="source_json_kw")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _input_path(args: argparse.Namespace) -> Path:
    if args.source_json is not None and args.source_json_kw is not None:
        raise ValueError("provide either positional source_json or --source-json, not both")
    if args.source_json is None and args.source_json_kw is None:
        return DEFAULT_SOURCE_JSON
    return args.source_json if args.source_json is not None else args.source_json_kw


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("payload must be object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def main() -> int:
    args = _parse_args()
    path = _input_path(args)
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        receipt = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(receipt, args.pretty))
        return 1

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append("status: must be ok|error")
    if not isinstance(payload.get("ok", True), bool) and "ok" in payload:
        errors.append("ok: if present must be bool")
    if payload.get("script") != SOURCE_CONTROL_CARD["C"]:
        errors.append(f"script: must be {SOURCE_CONTROL_CARD['C']!r}")
    if payload.get("control_card") != SOURCE_CONTROL_CARD:
        errors.append("control_card: must match canonical summary control card")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        expected = {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        }
        for key, value in expected.items():
            if authority.get(key) is not value:
                errors.append(f"authority.{key}: must be {value!r}")

    source_routes = payload.get("source_routes")
    if not isinstance(source_routes, dict):
        errors.append("source_routes: must be object")
        source_routes = {}
    missing = [name for name in EXPECTED_SOURCE_NAMES if name not in source_routes]
    extra = sorted(set(source_routes) - set(EXPECTED_SOURCE_NAMES))
    if missing:
        errors.append(f"source_routes: missing routes {missing!r}")
    if extra:
        errors.append(f"source_routes: unexpected routes {extra!r}")
    for name in EXPECTED_SOURCE_NAMES:
        route = source_routes.get(name)
        if not isinstance(route, dict):
            errors.append(f"source_routes.{name}: must be object")
            continue
        if route.get("present") is not True:
            errors.append(f"source_routes.{name}.present: must be true")
        if route.get("status") not in ALLOWED_STATUSES:
            errors.append(f"source_routes.{name}.status: must be ok|partial|error")
        for key in ("contract", "route_decision", "schema_version"):
            if not isinstance(route.get(key), str) or not route.get(key):
                errors.append(f"source_routes.{name}.{key}: must be non-empty string")

    rows = payload.get("bridge_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("bridge_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"bridge_rows[{index}]: must be object")
            continue
        if _nonnegative_int(row.get("frame")) is None:
            errors.append(f"bridge_rows[{index}].frame: must be nonnegative int")
        if row.get("wall1_unproved") is not False:
            errors.append(f"bridge_rows[{index}].wall1_unproved: must be false")
        if row.get("wall2_unproved") is not False:
            errors.append(f"bridge_rows[{index}].wall2_unproved: must be false")
        int_fields = ("triad_count", "mode_count")
        float_fields = (
            "phase_laplacian_gap",
            "negative_frame_ratio",
            "stability_margin",
            "low_frustration_basin_fraction",
            "basin_rarity",
            "best_frustration_floor",
        )
        for key in int_fields:
            value = row.get(key)
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"bridge_rows[{index}].{key}: must be nonnegative int or null")
        for key in float_fields:
            value = row.get(key)
            if value is not None and _finite_float(value) is None:
                errors.append(f"bridge_rows[{index}].{key}: must be finite or null")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    if _nonnegative_int(aggregate.get("shared_frame_count")) is None:
        errors.append("aggregate.shared_frame_count: must be nonnegative int")
    coverage = _finite_float(aggregate.get("coverage_fraction"))
    if coverage is None or coverage < 0.0 or coverage > 1.0 + 1.0e-12:
        errors.append("aggregate.coverage_fraction: must lie in [0,1]")
    for key in (
        "phase_laplacian_gap_mean",
        "stability_margin_mean",
        "low_frustration_basin_fraction_mean",
        "basin_rarity_mean",
        "best_frustration_floor_mean",
        "phase_gap_vs_rarity_correlation",
        "stability_vs_basin_fraction_correlation",
        "frustration_floor_vs_rarity_correlation",
    ):
        value = aggregate.get(key)
        if value is not None:
            parsed = _finite_float(value)
            if parsed is None:
                errors.append(f"aggregate.{key}: must be finite or null")
            elif "correlation" in key and (parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12):
                errors.append(f"aggregate.{key}: correlation must lie in [-1,1]")
    if aggregate.get("wall1_status") != "unproved":
        errors.append("aggregate.wall1_status: must be 'unproved'")
    if aggregate.get("wall1_proved") is not False:
        errors.append("aggregate.wall1_proved: must be false")
    if aggregate.get("wall2_status") != "unproved":
        errors.append("aggregate.wall2_status: must be 'unproved'")
    if aggregate.get("wall2_proved") is not False:
        errors.append("aggregate.wall2_proved: must be false")

    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "warnings": warnings,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
