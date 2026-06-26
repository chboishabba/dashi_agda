#!/usr/bin/env python3
"""Validate the sharp conditional TheoremG summary contract."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_theoremg_sharp_conditional_summary.py"
CONTRACT = "check_ns_theoremg_sharp_conditional_summary"
DEFAULT_INPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_theoremg_sharp_conditional_summary_20260620.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_theoremg_sharp_conditional_summary_check_20260620.json"
)

CONTROL_CARD = {
    "O": "Owner 5 validates the sharp conditional TheoremG summary contract.",
    "R": (
        "Require the CSV-backed summary to preserve positive H_area/H_B support, delta1 > 1, "
        "and a positive exponent margin."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail closed on missing keys, failed support flags, non-positive delta1, or non-positive exponent gap.",
    "L": "read summary json -> validate support flags and scalar thresholds -> emit deterministic JSON",
    "P": "FAIL_CLOSED_THEOREMG_SHARP_CONDITIONAL_SUMMARY_CHECK",
    "G": "This checker validates bookkeeping only and does not promote a theorem.",
    "F": "A valid summary must keep all support flags true and the merged frame count fixed.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _validate(payload: dict[str, Any]) -> tuple[list[str], dict[str, Any]]:
    errors: list[str] = []

    if payload.get("contract") != "ns_theoremg_sharp_conditional_summary":
        errors.append("unexpected summary contract")

    support = payload.get("hypothesis_support", {})
    flags = support.get("support_flags", {})
    for name in (
        "H_area_direct_positive",
        "H_area_isop_positive",
        "H_B_positive",
        "H_g12_positive",
        "H_g12_sharp_delta1_gt_1",
        "exponent_gap_positive",
        "reported_exp_gap_positive",
    ):
        if flags.get(name) is not True:
            errors.append(f"support flag failed: {name}")

    delta1_min = support.get("delta1_min")
    if not isinstance(delta1_min, (int, float)) or delta1_min <= 1.0:
        errors.append("delta1_min must be > 1")

    exponent = payload.get("exponent_comparison", {})
    margin = exponent.get("exponent_margin")
    if not isinstance(margin, (int, float)) or margin <= 0.0:
        errors.append("exponent_margin must be positive")

    merged_rows = payload.get("merged_rows")
    if not isinstance(merged_rows, list) or len(merged_rows) != 13:
        errors.append("merged_rows must contain 13 frames")

    details = {
        "status_field_ok": payload.get("status") == "ok",
        "support_flags": flags,
        "delta1_min": delta1_min,
        "exponent_margin": margin,
        "merged_row_count": len(merged_rows) if isinstance(merged_rows, list) else None,
    }
    return errors, details


def main() -> int:
    args = _parse_args()
    if not args.input_json.exists():
        raise FileNotFoundError(f"missing summary JSON: {args.input_json}")

    payload = json.loads(args.input_json.read_text(encoding="utf-8"))
    errors, details = _validate(payload)
    result = {
        "contract": CONTRACT,
        "control_card": CONTROL_CARD,
        "status": "error" if errors else "ok",
        "input_json": str(args.input_json),
        "details": details,
        "errors": errors,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(result, indent=2 if args.pretty else None, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
