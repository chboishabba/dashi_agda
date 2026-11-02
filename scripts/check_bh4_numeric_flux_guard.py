#!/usr/bin/env python3
"""Strict numeric-payability and HiGHS candidate regression, offline when absent."""
from __future__ import annotations

from copy import deepcopy

from acquire_bh4_parameter_evidence import normalize
from solve_bh4_flux_intervals import paid_bound, solve


def paid(pid: str, lower: float, upper: float, unit: str = "nmol/s") -> dict:
    return {
        "parameter_id": pid,
        "payment_status": "derived",
        "usable_for_joint_flux_witness": True,
        "lower": lower, "upper": upper, "unit": unit,
        "source_reference": "synthetic-regression-not-real-biochemistry",
        "same_object_reference": "fixture-cell",
        "compartment_reference": "fixture-compartment",
        "measurement_time_reference": "fixture-time",
        "directly_measured": False,
    }


def main() -> int:
    matrix = {
        "schema": "dashi.bh4-stoichiometric-matrix.v1",
        "reaction_index": ["RHEA:1"],
        "species_index": ["CHEBI:1"],
        "matrix": [[-1]],
    }
    a = paid("REACTION_FLUX:RHEA:1", 1.0, 2.0)
    b = paid("EXCHANGE:CHEBI:1", 1.0, 2.0)
    assert paid_bound(a) == (1.0, 2.0)
    manifest = {"parameters": [a, b]}
    result = normalize(manifest, matrix)
    assert result["summary"]["validation_errors"] == []
    assert result["summary"]["usable_for_joint_flux_witness"] == 2

    missing = deepcopy(manifest)
    missing["parameters"][0]["same_object_reference"] = None
    assert solve(matrix, missing)["status"] == "underdetermined"

    duplicated = deepcopy(manifest)
    duplicated["parameters"].append(deepcopy(duplicated["parameters"][0]))
    assert solve(matrix, duplicated)["status"] == "underdetermined"
    validated = normalize(duplicated, matrix)
    assert validated["summary"]["validation_errors"]
    reaction_row = next(r for r in validated["parameters"] if
                        r["parameter_id"] == "REACTION_FLUX:RHEA:1")
    assert reaction_row["payment_status"] == "unresolved"
    assert not reaction_row["usable_for_joint_flux_witness"]

    for invalid in (float("nan"), float("inf"), -float("inf")):
        malformed = deepcopy(manifest)
        malformed["parameters"][0]["lower"] = invalid
        assert paid_bound(malformed["parameters"][0]) is None
        assert solve(matrix, malformed)["status"] == "underdetermined"
        assert normalize(malformed, matrix)["summary"]["validation_errors"]
    reversed_bounds = deepcopy(manifest)
    reversed_bounds["parameters"][0]["lower"] = 3.0
    assert solve(matrix, reversed_bounds)["status"] == "underdetermined"

    mismatched = deepcopy(manifest)
    mismatched["parameters"][1]["unit"] = "molecules/hour"
    assert solve(matrix, mismatched)["status"] == "underdetermined"

    conditional = solve(matrix, manifest)
    assert conditional["status"] in ("feasible", "solver-unavailable")
    if conditional["status"] == "feasible":
        witness = conditional["candidate_flux_balance_witness"]
        assert witness["numeric_candidate_only"] is True
        assert witness["original_source_receipts_independently_authenticated"] is False
        assert abs(witness["reaction_flux"]["RHEA:1"] -
                   witness["external_exchange"]["CHEBI:1"]) <= witness["postcheck_tolerance"]
        assert witness["postcheck_max_balance_residual"] <= witness["postcheck_tolerance"]
        assert witness["postcheck_max_bound_violation"] <= witness["postcheck_tolerance"]
    print("BH4 normalized quantitative source-payment and numeric witness firewall: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
