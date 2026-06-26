#!/usr/bin/env python3
"""Validate the Calc 7 Reynolds boundary scan contract."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_calc7_reynolds_boundary_scan.py"
CONTRACT = "check_ns_calc7_reynolds_boundary_scan"
DEFAULT_INPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_calc7_reynolds_boundary_scan_N128_20260620.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_calc7_reynolds_boundary_scan_check_N128_20260620.json"
)

CONTROL_CARD = {
    "O": "Owner validates the Calc 7 Reynolds boundary scan contract.",
    "R": "Require authority/non-promotion integrity plus finite delta1 and boundary Bk minima on rows that claim successful boundary-Bk scans.",
    "C": SCRIPT_NAME,
    "S": "Fail closed on malformed schema, authority drift, non-finite successful-row minima, or inconsistent Reynolds-availability flags.",
    "L": "read scan json -> validate summary and successful rows -> emit deterministic JSON",
    "P": "FAIL_CLOSED_CALC7_REYNOLDS_BOUNDARY_SCAN_CHECK",
    "G": "This checker validates telemetry bookkeeping only and does not promote any theorem.",
    "F": "Residual degradation is allowed only when Reynolds labels or raw-archive Bk rows are unavailable and the payload says so explicitly.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _is_finite_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value))


def _validate(payload: dict[str, Any]) -> tuple[list[str], dict[str, Any]]:
    errors: list[str] = []

    if payload.get("contract") != "ns_calc7_reynolds_boundary_scan":
        errors.append("unexpected scan contract")

    authority = payload.get("authority", {})
    expected = {
        "candidate_only": True,
        "clay_authority": False,
        "empirical_non_promoting": True,
        "promoted": False,
        "runtime_authority": False,
        "theorem_authority": False,
        "truth_authority": False,
    }
    for key, value in expected.items():
        if authority.get(key) is not value:
            errors.append(f"authority mismatch: {key}")

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        errors.append("rows must be a non-empty list")
        rows = []

    ok_bk_rows = 0
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"row {index} is not an object")
            continue
        delta1 = row.get("delta1_min")
        if not _is_finite_number(delta1) or float(delta1) <= 0.0:
            errors.append(f"row {index} delta1_min must be finite positive")
        if row.get("boundary_bk_status") == "ok":
            ok_bk_rows += 1
            bk = row.get("boundary_bk_min")
            if not _is_finite_number(bk) or float(bk) <= 0.0:
                errors.append(f"row {index} boundary_bk_min must be finite positive when boundary_bk_status=ok")

    dataset = payload.get("dataset", {})
    reynolds_available = dataset.get("reynolds_label_available")
    reynolds_unavailable = dataset.get("reynolds_label_unavailable")
    if reynolds_available is reynolds_unavailable:
        errors.append("reynolds availability flags must be complementary")

    summary = payload.get("summary", {})
    if summary.get("ok_boundary_bk_rows") != ok_bk_rows:
        errors.append("ok_boundary_bk_rows summary mismatch")

    details = {
        "status": payload.get("status"),
        "row_count": len(rows),
        "ok_boundary_bk_rows": ok_bk_rows,
        "reynolds_label_available": reynolds_available,
        "delta1_min_global": summary.get("delta1_min_global"),
        "boundary_bk_min_global": summary.get("boundary_bk_min_global"),
    }
    return errors, details


def main() -> int:
    args = _parse_args()
    payload = json.loads(args.input_json.read_text(encoding="utf-8"))
    errors, details = _validate(payload)
    result = {
        "contract": CONTRACT,
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "status": "error" if errors else "ok",
        "input_json": str(args.input_json),
        "details": details,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(result, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
