#!/usr/bin/env python3
"""Validate ns_boundary_pressure_q_bridge_summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_boundary_pressure_q_bridge_summary.py"
CONTRACT = "check_ns_boundary_pressure_q_bridge_summary"
SOURCE_CONTRACT = "ns_boundary_pressure_q_bridge_summary"
CHECK_ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_PRESSURE_Q_BRIDGE_SUMMARY_CHECK"

DEFAULT_SUMMARY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_pressure_q_bridge_summary_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_boundary_pressure_q_bridge_summary_20260621.json"
)

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

CONTROL_CARD = {
    "O": "Validate boundary pressure/Q bridge summary output.",
    "R": "Check source ledger, bridge rows, aggregate correlations, and authority flags.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: malformed summary structure is an error.",
    "L": "Load bridge JSON, validate sources and rows, then emit a checker receipt.",
    "P": CHECK_ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field or inconsistent threshold row is treated as a hard failure.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summary-json", type=Path, default=DEFAULT_SUMMARY_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("summary payload must be object")
    return payload


def _finite_float(value: Any) -> float | None:
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


def _check_fraction(errors: list[str], path: str, value: Any) -> None:
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        errors.append(f"{path}: must be finite fraction in [0,1]")


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(args.summary_json)
    except Exception as exc:  # noqa: BLE001
        receipt = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": CHECK_ROUTE_DECISION,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(receipt, args.pretty))
        return 1

    for key in CHECK_CARD_KEYS:
        if not isinstance(payload.get(key), str) or not payload.get(key, "").strip():
            errors.append(f"{key}: must be non-empty string")
    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("status") not in {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}:
        errors.append("status: must be ok|partial|error")

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
        for key, expected_value in expected.items():
            if authority.get(key) is not expected_value:
                errors.append(f"authority.{key}: must be {expected_value!r}")

    status_by_source = payload.get("status_by_source")
    if not isinstance(status_by_source, dict):
        errors.append("status_by_source: must be object")
    else:
        for source in ("boundary_pressure", "boundary_delta1", "pressure_gap"):
            entry = status_by_source.get(source)
            if not isinstance(entry, dict):
                errors.append(f"status_by_source.{source}: must be object")
                continue
            if not isinstance(entry.get("path"), str) or not entry.get("path"):
                errors.append(f"status_by_source.{source}.path: must be non-empty string")
            if entry.get("status") not in {"ok", "partial", "missing", "error", "missing_required_field"}:
                warnings.append(f"status_by_source.{source}.status is unexpected")
            if not isinstance(entry.get("present"), bool):
                errors.append(f"status_by_source.{source}.present: must be bool")
            if _nonnegative_int(entry.get("bin_count")) is None:
                errors.append(f"status_by_source.{source}.bin_count: must be nonnegative int")

    shared_thresholds = payload.get("shared_thresholds")
    if not isinstance(shared_thresholds, list) or not shared_thresholds:
        errors.append("shared_thresholds: must be non-empty list")
        shared_thresholds = []

    bridge_rows = payload.get("bridge_rows")
    if not isinstance(bridge_rows, list) or not bridge_rows:
        errors.append("bridge_rows: must be non-empty list")
        bridge_rows = []
    for index, row in enumerate(bridge_rows):
        if not isinstance(row, dict):
            errors.append(f"bridge_rows[{index}]: must be object")
            continue
        if _finite_float(row.get("delta1_threshold")) is None:
            errors.append(f"bridge_rows[{index}].delta1_threshold: must be finite")
        for key in (
            "boundary_q_negative_fraction",
            "boundary_p11_negative_fraction",
            "boundary_omega2_dominant_fraction",
        ):
            _check_fraction(errors, f"bridge_rows[{index}].{key}", row.get(key))
        for key in (
            "boundary_q_mean",
            "boundary_p11_mean",
            "pressure_gap_p12_scaled_mean",
            "boundary_delta1_min",
            "boundary_gap_separation",
        ):
            value = row.get(key)
            if value is not None and _finite_float(value) is None:
                errors.append(f"bridge_rows[{index}].{key}: must be null or finite")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    if _nonnegative_int(aggregate.get("threshold_count")) is None:
        errors.append("aggregate.threshold_count: must be nonnegative int")
    for key in ("q_negative_fraction_mean", "p11_negative_fraction_mean"):
        _check_fraction(errors, f"aggregate.{key}", aggregate.get(key))
    for key in (
        "q_vs_p11_negative_fraction_correlation",
        "q_vs_pressure_gap_p12_scaled_mean_correlation",
        "abs_q_mean_vs_boundary_delta1_min_correlation",
    ):
        value = aggregate.get(key)
        if value is not None:
            parsed = _finite_float(value)
            if parsed is None or parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12:
                errors.append(f"aggregate.{key}: must be null or finite in [-1,1]")

    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": CHECK_ROUTE_DECISION,
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
