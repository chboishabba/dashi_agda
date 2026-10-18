#!/usr/bin/env python3
"""Validate fail-closed output from ns_r650_quantitative_stress_scan.py."""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SOURCE_SCRIPT_NAME = "scripts/ns_r650_quantitative_stress_scan.py"
SOURCE_CONTRACT = "ns_r650_quantitative_stress_scan"
CHECK_CONTRACT = "check_ns_r650_quantitative_stress_scan"


def _finite_or_none(value: Any) -> bool:
    return value is None or (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def validate(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append("unexpected source script")
    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append("unexpected source contract")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("missing authority object")
    else:
        required_true = (
            "finite_galerkin_diagnostic",
            "literal_max_norm_dyadic_weights",
            "r647_abel_identity_numeric_check",
        )
        required_false = (
            "r406_evaluated",
            "c1_evaluated",
            "c2_theorem_authority",
            "continuum_authority",
            "clay_authority",
            "promoted",
        )
        for key in required_true:
            if authority.get(key) is not True:
                errors.append(f"authority.{key} must be true")
        for key in required_false:
            if authority.get(key) is not False:
                errors.append(f"authority.{key} must be false")

    tested = payload.get("tested_statement")
    if not isinstance(tested, dict):
        errors.append("missing tested_statement")
    elif tested.get("actual_r650_c2_evaluated") is not False:
        errors.append("actual R650 C2 must remain explicitly untested")

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        errors.append("rows must be a nonempty list")
        rows = []

    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"row {index} is not an object")
            continue
        if row.get("actual_c2_tested") is not False:
            errors.append(f"row {index} falsely claims actual C2 test")
        if row.get("r406_required_for_actual_c2") is not True:
            errors.append(f"row {index} must preserve R406 requirement")
        for key in (
            "literal_unweighted_nonlinear_transfer",
            "literal_weighted_transfer_W",
            "literal_critical_production_rate_2W",
            "literal_critical_dissipation_rate",
            "literal_strict_surplus_rate",
            "abel_identity_absolute_residual",
            "conservative_layer_cake_absolute_residual",
        ):
            if not _finite_or_none(row.get(key)):
                errors.append(f"row {index} has nonfinite {key}")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("missing aggregate object")
    else:
        if aggregate.get("actual_c2_status") != "not-tested-r406-evaluator-required":
            errors.append("aggregate must keep actual C2 fail-closed")
        if aggregate.get("row_count") != len(rows):
            errors.append("aggregate row_count mismatch")
        for key in (
            "minimum_viscosity_only_margin_capacity",
            "maximum_viscosity_only_margin_capacity",
            "maximum_abel_identity_absolute_residual",
            "maximum_unweighted_conservation_residual",
        ):
            if not _finite_or_none(aggregate.get(key)):
                errors.append(f"aggregate has nonfinite {key}")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", type=Path)
    args = parser.parse_args()

    payload = json.loads(args.input_json.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        print(json.dumps({"contract": CHECK_CONTRACT, "status": "error", "errors": ["root must be object"]}))
        return 1
    errors = validate(payload)
    result = {
        "contract": CHECK_CONTRACT,
        "source": str(args.input_json),
        "status": "ok" if not errors else "error",
        "errors": errors,
    }
    print(json.dumps(result, sort_keys=True))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
