#!/usr/bin/env python3
"""Validate ns_boundary_pressure_gate_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_boundary_pressure_gate_scan.py"
CONTRACT = "check_ns_boundary_pressure_gate_scan"
SCAN_CONTRACT = "ns_boundary_pressure_gate_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_PRESSURE_GATE_SCAN"
CHECK_ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_PRESSURE_GATE_SCAN_CHECK"

DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_boundary_pressure_gate_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_boundary_pressure_gate_scan_N128_20260621.json"
)

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}
CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

CONTROL_CARD = {
    "O": "Validate boundary pressure-gate scan schema and arithmetic.",
    "R": "Check control card, authority flags, frame rows, aggregate rows, and boundary fractions.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: malformed schema or arithmetic drift is an error.",
    "L": "Load scan JSON, validate frame rows and threshold rows, then emit a checker receipt.",
    "P": CHECK_ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field, invalid fraction, or contract mismatch is treated as a hard failure.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-json", type=Path, default=DEFAULT_SCAN_JSON)
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
        raise ValueError("scan payload must be object")
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


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            errors.append(f"{key}: must be non-empty string")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
        return
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


def _check_threshold_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    if _finite_float(row.get("delta1_threshold")) is None:
        errors.append(f"{path}.delta1_threshold: must be finite")
    active_count = _nonnegative_int(row.get("active_count"))
    if active_count is None:
        errors.append(f"{path}.active_count: must be nonnegative int")
        active_count = 0
    for key in (
        "active_fraction_of_boundary",
        "q_negative_fraction",
        "p11_negative_fraction",
        "omega2_dominant_fraction",
    ):
        _check_fraction(errors, f"{path}.{key}", row.get(key))
    for key in ("q_mean", "p11_mean", "p22_mean", "p33_mean", "h_mean"):
        if _finite_float(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be finite")
    if active_count == 0 and row.get("delta1_min") is not None and _finite_float(row.get("delta1_min")) is None:
        errors.append(f"{path}.delta1_min: must be null or finite")


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(args.scan_json)
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

    _check_control_card(payload, errors)
    if payload.get("contract") != SCAN_CONTRACT:
        errors.append(f"contract: must be {SCAN_CONTRACT!r}")
    if payload.get("route_decision") != SCAN_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SCAN_ROUTE_DECISION!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append(f"status: must be one of {sorted(ALLOWED_STATUSES)!r}")
    _check_authority(payload, errors)

    frame_rows = payload.get("frame_rows")
    if not isinstance(frame_rows, list) or not frame_rows:
        errors.append("frame_rows: must be a non-empty list")
        frame_rows = []
    for index, row in enumerate(frame_rows):
        if not isinstance(row, dict):
            errors.append(f"frame_rows[{index}]: must be object")
            continue
        if row.get("status") not in ALLOWED_STATUSES:
            errors.append(f"frame_rows[{index}].status: invalid status")
        if _nonnegative_int(row.get("boundary_cell_count")) is None:
            errors.append(f"frame_rows[{index}].boundary_cell_count: must be nonnegative int")
        _check_fraction(errors, f"frame_rows[{index}].boundary_fraction", row.get("boundary_fraction"))
        _check_fraction(errors, f"frame_rows[{index}].q_negative_fraction", row.get("q_negative_fraction", 0.0))
        threshold_rows = row.get("threshold_rows")
        if not isinstance(threshold_rows, list):
            errors.append(f"frame_rows[{index}].threshold_rows: must be list")
        else:
            for j, threshold_row in enumerate(threshold_rows):
                if not isinstance(threshold_row, dict):
                    errors.append(f"frame_rows[{index}].threshold_rows[{j}]: must be object")
                    continue
                _check_threshold_row(threshold_row, f"frame_rows[{index}].threshold_rows[{j}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    if _nonnegative_int(aggregate.get("processed_frames")) is None:
        errors.append("aggregate.processed_frames: must be nonnegative int")
    if _nonnegative_int(aggregate.get("ok_frames")) is None:
        errors.append("aggregate.ok_frames: must be nonnegative int")
    threshold_rows = aggregate.get("boundary_threshold_rows")
    if not isinstance(threshold_rows, list) or not threshold_rows:
        errors.append("aggregate.boundary_threshold_rows: must be non-empty list")
        threshold_rows = []
    for index, row in enumerate(threshold_rows):
        if not isinstance(row, dict):
            errors.append(f"aggregate.boundary_threshold_rows[{index}]: must be object")
            continue
        _check_threshold_row(row, f"aggregate.boundary_threshold_rows[{index}]", errors)

    for key in (
        "q_negative_fraction_mean",
        "p11_negative_fraction_mean",
        "omega2_dominant_fraction_mean",
    ):
        _check_fraction(errors, f"aggregate.{key}", aggregate.get(key))
    corr = aggregate.get("q_vs_p11_negative_fraction_correlation")
    if corr is not None:
        corr_value = _finite_float(corr)
        if corr_value is None or corr_value < -1.0 - 1.0e-12 or corr_value > 1.0 + 1.0e-12:
            errors.append("aggregate.q_vs_p11_negative_fraction_correlation: must be null or in [-1,1]")

    ok = not errors
    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": CHECK_ROUTE_DECISION,
        "scan_contract": payload.get("contract"),
        "status": OK_STATUS if ok else ERROR_STATUS,
        "ok": ok,
        "warnings": warnings,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
