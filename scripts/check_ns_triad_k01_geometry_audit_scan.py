#!/usr/bin/env python3
"""Validate ns_triad_k01_geometry_audit_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_k01_geometry_audit_scan.py"
CONTRACT = "check_ns_triad_k01_geometry_audit_scan"
SOURCE_CONTRACT = "ns_triad_k01_geometry_audit_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_k01_geometry_audit_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_K01_GEOMETRY_AUDIT_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_K01_GEOMETRY_AUDIT_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_k01_geometry_audit_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_k01_geometry_audit_scan_N128_20260621.json"
)

SOURCE_CONTROL_CARD = {
    "O": "Measure K01 geometry audit telemetry for the active NS triad Wall 1 route.",
    "R": (
        "Record K01 geometry ratios, directional proxies, and frame-shell consistency "
        "as candidate-only fail-closed telemetry."
    ),
    "C": SOURCE_SCRIPT_NAME,
    "S": "Candidate-only telemetry; the K01 geometry audit is empirical and non-promoting.",
    "L": "Load the audit rows, validate bounded metrics, and expose the wall as unproved.",
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this audit scan.",
    "F": "K01 geometry telemetry is diagnostic only; fail-closed status is not a proof.",
}

CONTROL_CARD = {
    "O": "Validate the K01 geometry audit scan output.",
    "R": "Check control card, authority flags, bounded metrics, and fail-closed closure markers.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed K01 geometry telemetry surfaces.",
    "L": "Load the audit JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field, authority drift, or route-marker mismatch is a hard error.",
}

EXPECTED_AUTHORITY = {
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
    if not path.exists():
        raise FileNotFoundError(f"missing input json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: payload must be object")
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


def _fraction(value: Any) -> float | None:
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        return None
    return parsed


def _check_metric_range(
    errors: list[str],
    path: str,
    value: Any,
    *,
    lower: float | None = 0.0,
    upper: float | None = None,
) -> None:
    parsed = _finite_float(value)
    if parsed is None:
        errors.append(f"{path}: must be finite")
        return
    if lower is not None and parsed < lower - 1.0e-12:
        errors.append(f"{path}: must be >= {lower}")
    if upper is not None and parsed > upper + 1.0e-12:
        errors.append(f"{path}: must be <= {upper}")


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    if row.get("status") not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    if _nonnegative_int(row.get("shell")) is None and _nonnegative_int(row.get("shell_n")) is None:
        errors.append(f"{path}.shell: must be nonnegative int")
    for key in ("candidate_only", "empirical_non_promoting"):
        if row.get(key) is not True:
            errors.append(f"{path}.{key}: must be true")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    if row.get("fail_closed") is not True:
        errors.append(f"{path}.fail_closed: must be true")

    for key in ("selected_mode_count", "triad_count", "geometry_bin_count"):
        if key in row and _nonnegative_int(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int or null")

    geometry_fields = (
        ("k01_geometry_ratio", 0.0, 1.0),
        ("k01_ratio_proxy", 0.0, 1.0),
        ("frame_geometry_proxy", 0.0, None),
        ("directional_gap_proxy", 0.0, None),
        ("directional_gap_lower_bound", 0.0, None),
        ("directional_gap_residual", 0.0, None),
        ("geometry_stability_proxy", 0.0, None),
        ("geometry_alignment_proxy", 0.0, None),
        ("shell_curvature_proxy", 0.0, None),
    )
    seen_any = False
    for key, lower, upper in geometry_fields:
        if key in row:
            seen_any = True
            _check_metric_range(errors, f"{path}.{key}", row.get(key), lower=lower, upper=upper)
    if not seen_any:
        errors.append(f"{path}: must contain at least one geometry metric field")

    if row.get("warnings") is not None and not isinstance(row.get("warnings"), list):
        errors.append(f"{path}.warnings: must be list or null")
    if row.get("errors") is not None and not isinstance(row.get("errors"), list):
        errors.append(f"{path}.errors: must be list or null")


def _check_aggregate(aggregate: dict[str, Any], row_count: int, errors: list[str]) -> None:
    if _nonnegative_int(aggregate.get("processed_rows")) != row_count:
        errors.append("aggregate.processed_rows: must match row count")
    for key in ("ok_rows", "partial_rows", "error_rows"):
        if _nonnegative_int(aggregate.get(key)) is None:
            errors.append(f"aggregate.{key}: must be nonnegative int")
    if aggregate.get("wall1_status") not in (None, "unproved"):
        errors.append("aggregate.wall1_status: if present must be 'unproved'")
    if aggregate.get("fail_closed") is not True:
        errors.append("aggregate.fail_closed: must be true")

    for key in (
        "k01_geometry_ratio_mean",
        "k01_geometry_ratio_max",
        "frame_geometry_proxy_mean",
        "directional_gap_proxy_mean",
        "directional_gap_lower_bound_mean",
        "directional_gap_residual_mean",
        "geometry_stability_proxy_mean",
        "geometry_alignment_proxy_mean",
    ):
        value = aggregate.get(key)
        if value is not None:
            if _finite_float(value) is None:
                errors.append(f"aggregate.{key}: must be finite or null")

    for key in ("k01_geometry_ratio_mean", "k01_geometry_ratio_max"):
        value = _fraction(aggregate.get(key))
        if value is None and aggregate.get(key) is not None:
            errors.append(f"aggregate.{key}: must be within [0,1]")

    for key in (
        "frame_geometry_proxy_mean",
        "directional_gap_proxy_mean",
        "directional_gap_lower_bound_mean",
        "directional_gap_residual_mean",
        "geometry_stability_proxy_mean",
        "geometry_alignment_proxy_mean",
    ):
        value = _finite_float(aggregate.get(key))
        if value is not None and value < -1.0e-12:
            errors.append(f"aggregate.{key}: must be nonnegative when present")

    if aggregate.get("candidate_only") is not True:
        errors.append("aggregate.candidate_only: must be true")
    if aggregate.get("empirical_non_promoting") is not True:
        errors.append("aggregate.empirical_non_promoting: must be true")


def main() -> int:
    args = _parse_args()
    source_json = _input_path(args)
    errors: list[str] = []

    try:
        payload = _load_json(source_json)
    except Exception as exc:  # noqa: BLE001
        receipt = {
            "contract": CONTRACT,
            "schema_version": SCHEMA_VERSION,
            "route_decision": ROUTE_DECISION,
            "script_name": SCRIPT_NAME,
            "control_card": CONTROL_CARD,
            "source_json": str(source_json),
            "status": ERROR_STATUS,
            "ok": False,
            "error_count": 1,
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
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("control_card") != SOURCE_CONTROL_CARD:
        errors.append("control_card: must exactly match the source control card")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append("status: must be ok|partial|error")
    if not isinstance(payload.get("ok"), bool):
        errors.append("ok: must be bool")
    if payload.get("fail_closed") is not True:
        errors.append("fail_closed: must be true")
    if payload.get("candidate_only") is not True:
        errors.append("candidate_only: must be true")
    if payload.get("empirical_non_promoting") is not True:
        errors.append("empirical_non_promoting: must be true")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        for key, expected in EXPECTED_AUTHORITY.items():
            if authority.get(key) is not expected:
                errors.append(f"authority.{key}: must be {expected!r}")

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        errors.append("rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"rows[{index}]: must be object")
            continue
        _check_row(row, f"rows[{index}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        _check_aggregate(aggregate, len(rows), errors)

    status = OK_STATUS if not errors else ERROR_STATUS
    receipt = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "source_json": str(source_json),
        "status": status,
        "ok": status == OK_STATUS,
        "error_count": int(len(errors)),
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
