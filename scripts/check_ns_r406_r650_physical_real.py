#!/usr/bin/env python3
"""Validate fail-closed authority for R406/R650 physical-real diagnostics."""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

R406_CONTRACT = "ns_r406_physical_real_eval"
C2_CONTRACT = "ns_r650_c2_physical_real_scan"
C1_CONTRACT = "ns_r650_c1_physical_real_scan"
CHECK_CONTRACT = "check_ns_r406_r650_physical_real"


def _finite(value: Any) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def _check_authority(authority: Any, *, prefix: str, errors: list[str]) -> None:
    if not isinstance(authority, dict):
        errors.append(f"{prefix}: missing authority object")
        return
    required_false = (
        "formal_rational_helical_same_object",
        "agda_kernel_authority",
        "continuum_authority",
        "clay_authority",
        "promoted",
    )
    for key in required_false:
        if authority.get(key) is not False:
            errors.append(f"{prefix}: authority.{key} must be false")


def validate_r406(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("contract") != R406_CONTRACT:
        errors.append("unexpected R406 contract")
    _check_authority(payload.get("authority"), prefix="r406", errors=errors)

    state = payload.get("state")
    if not isinstance(state, dict):
        errors.append("r406: missing state metadata")
    else:
        if state.get("zero_mode_forcing_enforced") is not True:
            errors.append("r406: zero-mode forcing convention not enforced")
        for key in (
            "retained_divergence_max_residual",
            "pre_enforcement_zero_mode_forcing_residual",
        ):
            if not _finite(state.get(key)):
                errors.append(f"r406: state.{key} must be finite")

    predicted = payload.get("predicted_pair_count")
    evaluated = payload.get("evaluated_pair_count")
    if not isinstance(predicted, int) or predicted < 0:
        errors.append("r406: predicted_pair_count must be nonnegative integer")
    if not isinstance(evaluated, int) or evaluated < 0:
        errors.append("r406: evaluated_pair_count must be nonnegative integer")
    if predicted != evaluated:
        errors.append("r406: pair counts disagree")

    for key in (
        "global_direct_companion",
        "r406_weighted_remainder",
        "global_forcing_full",
        "c1_instantaneous_four_forcing_full",
        "offdiagonal_minus_twice_direct_companion",
        "c1_r406_diagonal_coupling_residual",
    ):
        if not _finite(payload.get(key)):
            errors.append(f"r406: {key} must be finite")

    minimum_rate = payload.get("minimum_pair_rate")
    if minimum_rate is not None and (not _finite(minimum_rate) or float(minimum_rate) <= 0.0):
        errors.append("r406: minimum_pair_rate must be positive when present")
    return errors


def _validate_c2_row(row: Any, *, label: str, errors: list[str]) -> None:
    if not isinstance(row, dict):
        errors.append(f"{label}: row must be object")
        return
    r406_authority = row.get("r406_authority")
    _check_authority(r406_authority, prefix=f"{label}.r406", errors=errors)

    for key in (
        "production_rate_2W",
        "critical_dissipation_rate",
        "r406_weighted_remainder",
        "strict_surplus_rate",
        "r406_minus_strict_surplus",
        "unweighted_conservation_residual",
    ):
        if not _finite(row.get(key)):
            errors.append(f"{label}: {key} must be finite")

    if not isinstance(row.get("r406_evaluated_pair_count"), int):
        errors.append(f"{label}: r406_evaluated_pair_count must be integer")

    packet_split = row.get("packet_split")
    if packet_split is not None:
        if not isinstance(packet_split, dict):
            errors.append(f"{label}: packet_split must be object")
        else:
            for key in (
                "collar_layer_cake",
                "remote_layer_cake",
                "physical_upper_layer_cake",
                "upper_minus_collar_remote_layer_cake",
                "abel_reconstruction_residual",
                "maximum_three_region_flux_residual",
                "maximum_upper_split_residual",
                "maximum_remote_spectral_cross",
                "maximum_cross_split_residual",
            ):
                if not _finite(packet_split.get(key)):
                    errors.append(f"{label}: packet_split.{key} must be finite")
            if not isinstance(packet_split.get("remote_spectral_cross_violation_count"), int):
                errors.append(
                    f"{label}: packet_split.remote_spectral_cross_violation_count "
                    "must be integer"
                )
            if not isinstance(packet_split.get("full_cross_below_collar_violation_count"), int):
                errors.append(
                    f"{label}: packet_split.full_cross_below_collar_violation_count "
                    "must be integer"
                )
            if packet_split.get("authority") != (
                "finite-floating-packet-decomposition-diagnostic-only"
            ):
                errors.append(f"{label}: packet_split authority must remain diagnostic")


def _validate_c1_row(row: Any, *, label: str, errors: list[str]) -> None:
    if not isinstance(row, dict):
        errors.append(f"{label}: row must be object")
        return
    for key in (
        "global_forcing_full",
        "c1_integrand_four_forcing_full",
        "forcing_full_diagonal",
        "forcing_full_offdiagonal",
        "offdiagonal_minus_twice_direct_companion",
        "c1_r406_diagonal_coupling_residual",
        "r406_weighted_remainder",
    ):
        if not _finite(row.get(key)):
            errors.append(f"{label}: {key} must be finite")
    minimum_rate = row.get("minimum_pair_rate")
    if minimum_rate is not None and (
        not _finite(minimum_rate) or float(minimum_rate) <= 0.0
    ):
        errors.append(f"{label}: minimum_pair_rate must be positive when present")


def validate_c1(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("contract") != C1_CONTRACT:
        errors.append("unexpected C1 contract")
    authority = payload.get("authority")
    _check_authority(authority, prefix="c1", errors=errors)
    if isinstance(authority, dict):
        if authority.get("cutoff_uniform_bound_proved") is not False:
            errors.append("c1: cutoff_uniform_bound_proved must remain false")
        if authority.get("finite_cutoff_comparison_only") is not True:
            errors.append("c1: finite_cutoff_comparison_only must be true")

    status = payload.get("formal_theorem_status")
    if status != "not-proved-finite-cutoff-physical-real-diagnostic-only":
        errors.append("c1: formal theorem status must remain fail-closed")

    if "row" in payload:
        _validate_c1_row(payload.get("row"), label="c1.row", errors=errors)

    runs = payload.get("runs")
    if runs is not None:
        if not isinstance(runs, list):
            errors.append("c1: runs must be list")
        else:
            for ri, run in enumerate(runs):
                if not isinstance(run, dict):
                    errors.append(f"c1.run[{ri}] must be object")
                    continue
                rows = run.get("rows")
                if not isinstance(rows, list):
                    errors.append(f"c1.run[{ri}].rows must be list")
                    continue
                for si, row in enumerate(rows):
                    _validate_c1_row(
                        row,
                        label=f"c1.run[{ri}].row[{si}]",
                        errors=errors,
                    )

    comparison = payload.get("cutoff_comparison")
    if comparison is not None:
        if not isinstance(comparison, dict):
            errors.append("c1: cutoff_comparison must be object")
        elif comparison.get("finite_sample_supports_uniform_bound_theorem") is not False:
            errors.append("c1: finite sample must not claim a uniform theorem")
    return errors


def validate_c2(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if payload.get("contract") != C2_CONTRACT:
        errors.append("unexpected C2 contract")
    _check_authority(payload.get("authority"), prefix="c2", errors=errors)

    status = payload.get("formal_theorem_status")
    aggregate = payload.get("aggregate")
    if status is None and isinstance(aggregate, dict):
        status = aggregate.get("formal_theorem_status")
    if status != "not-proved-numerical-physical-real-diagnostic-only":
        errors.append("c2: formal theorem status must remain fail-closed")

    if "row" in payload:
        _validate_c2_row(payload.get("row"), label="c2.row", errors=errors)

    runs = payload.get("runs")
    if runs is not None:
        if not isinstance(runs, list):
            errors.append("c2: runs must be list")
        else:
            for ri, run in enumerate(runs):
                if not isinstance(run, dict):
                    errors.append(f"c2.run[{ri}] must be object")
                    continue
                rows = run.get("rows")
                if not isinstance(rows, list):
                    errors.append(f"c2.run[{ri}].rows must be list")
                    continue
                for si, row in enumerate(rows):
                    _validate_c2_row(
                        row,
                        label=f"c2.run[{ri}].row[{si}]",
                        errors=errors,
                    )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", type=Path)
    args = parser.parse_args()

    payload = json.loads(args.input_json.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        result = {
            "contract": CHECK_CONTRACT,
            "status": "error",
            "errors": ["root must be object"],
        }
        print(json.dumps(result, sort_keys=True))
        return 1

    contract = payload.get("contract")
    if contract == R406_CONTRACT:
        errors = validate_r406(payload)
    elif contract == C2_CONTRACT:
        errors = validate_c2(payload)
    elif contract == C1_CONTRACT:
        errors = validate_c1(payload)
    else:
        errors = [f"unsupported contract {contract!r}"]

    result = {
        "contract": CHECK_CONTRACT,
        "source": str(args.input_json),
        "source_contract": contract,
        "status": "ok" if not errors else "error",
        "errors": errors,
    }
    print(json.dumps(result, sort_keys=True))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
