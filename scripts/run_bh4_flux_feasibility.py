#!/usr/bin/env python3
"""Check a supplied BH4 flux candidate against S*v + external_exchange = 0.

This is a witness checker, not an optimiser.  It returns:
  feasible        supplied complete candidate satisfies bounds and balance;
  infeasible      supplied complete candidate violates a bound/balance;
  underdetermined required bounds/candidate/exchange coordinates are missing.

`infeasible` therefore means *this supplied candidate* is infeasible, not that no
other feasible flux vector exists.
"""

from __future__ import annotations

import argparse
import csv
import json
from fractions import Fraction
from pathlib import Path


def number(value: object) -> Fraction:
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        return Fraction(str(value))
    return Fraction(str(value))


def parameter_map(parameters: dict) -> dict[str, dict]:
    return {str(row.get("parameter_id")): row for row in parameters.get("parameters", []) if row.get("parameter_id")}


def flux_bound_for(rhea_id: str, pmap: dict[str, dict]) -> dict | None:
    for key in (f"REACTION_FLUX:{rhea_id}", f"FLUX:{rhea_id}", rhea_id):
        row = pmap.get(key)
        if row and row.get("payment_status") != "unresolved":
            return row
    return None


def evaluate(matrix_receipt: dict, parameter_receipt: dict, candidate: dict) -> dict:
    reactions = list(matrix_receipt.get("reaction_index", []))
    species = list(matrix_receipt.get("species_index", []))
    matrix = matrix_receipt.get("matrix", [])
    pmap = parameter_map(parameter_receipt)
    candidate_flux = candidate.get("reaction_flux", {})
    external_exchange = candidate.get("external_exchange", {})

    missing_flux_bounds: list[str] = []
    missing_flux_values: list[str] = []
    bound_violations: list[dict] = []
    flux_vector: list[Fraction] = []

    for rid in reactions:
        bound = flux_bound_for(rid, pmap)
        if bound is None:
            missing_flux_bounds.append(rid)
        if rid not in candidate_flux:
            missing_flux_values.append(rid)
            flux_vector.append(Fraction(0))
            continue
        value = number(candidate_flux[rid])
        flux_vector.append(value)
        if bound is not None:
            lower = number(bound["lower"])
            upper = number(bound["upper"])
            if not (lower <= value <= upper):
                bound_violations.append({"rhea_id": rid, "value": str(value), "lower": str(lower), "upper": str(upper)})

    missing_exchange = [sid for sid in species if sid not in external_exchange]
    balances: list[dict] = []
    nonzero_balance: list[dict] = []
    if len(matrix) == len(species) and all(len(row) == len(reactions) for row in matrix):
        for i, sid in enumerate(species):
            internal = sum((Fraction(int(matrix[i][j])) * flux_vector[j] for j in range(len(reactions))), Fraction(0))
            exchange = number(external_exchange.get(sid, 0))
            total = internal + exchange
            row = {"species": sid, "internal": str(internal), "external_exchange": str(exchange), "total": str(total)}
            balances.append(row)
            if total != 0:
                nonzero_balance.append(row)
    else:
        return {
            "schema": "dashi.bh4-flux-feasibility.v1",
            "status": "underdetermined",
            "reason": "matrix dimensions invalid",
            "candidate_flux_balance_witness": None,
            "missing_flux_bounds": reactions,
            "promotion_boundary": promotion_boundary(),
        }

    incomplete = bool(missing_flux_bounds or missing_flux_values or missing_exchange)
    if incomplete:
        status = "underdetermined"
    elif bound_violations or nonzero_balance:
        status = "infeasible"
    else:
        status = "feasible"

    witness = None
    if status == "feasible":
        witness = {
            "reaction_flux": {rid: str(flux_vector[j]) for j, rid in enumerate(reactions)},
            "external_exchange": {sid: str(number(external_exchange[sid])) for sid in species},
            "balance_rows": balances,
            "same_state_reference": candidate.get("same_state_reference"),
            "measurement_reference": candidate.get("measurement_reference"),
        }

    return {
        "schema": "dashi.bh4-flux-feasibility.v1",
        "status": status,
        "reaction_count": len(reactions),
        "species_count": len(species),
        "missing_flux_bounds": missing_flux_bounds,
        "missing_flux_values": missing_flux_values,
        "missing_external_exchange": missing_exchange,
        "bound_violations": bound_violations,
        "nonzero_balance": nonzero_balance,
        "candidate_flux_balance_witness": witness,
        "external_exchange": external_exchange,
        "promotion_boundary": promotion_boundary(),
    }


def promotion_boundary() -> dict:
    return {
        "missing_flux_bound_substituted_with_zero": False,
        "candidate_infeasible_proves_system_infeasible": False,
        "feasible_flux_state_proves_allocator_causality": False,
        "feasible_flux_state_proves_disease_mechanism": False,
        "external_exchange_collapsed_into_internal_stoichiometry": False,
    }


def write_outputs(result: dict, prefix: Path) -> None:
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix(".json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with prefix.with_suffix(".csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["species", "internal", "external_exchange", "total"])
        writer.writeheader()
        witness = result.get("candidate_flux_balance_witness") or {}
        for row in witness.get("balance_rows", []):
            writer.writerow(row)
    lines = [
        "# BH4 joint flux feasibility receipt",
        "",
        f"- status: `{result['status']}`",
        f"- missing flux bounds: {len(result.get('missing_flux_bounds', []))}",
        f"- missing flux values: {len(result.get('missing_flux_values', []))}",
        f"- missing external exchange coordinates: {len(result.get('missing_external_exchange', []))}",
        f"- candidate flux balance witness: `{result.get('candidate_flux_balance_witness') is not None}`",
        "",
        "A feasible supplied candidate is not by itself a disease-mechanism or allocator-causality proof.",
    ]
    prefix.with_suffix(".md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--parameters", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output-prefix", type=Path)
    args = parser.parse_args()
    result = evaluate(
        json.loads(args.matrix.read_text(encoding="utf-8")),
        json.loads(args.parameters.read_text(encoding="utf-8")),
        json.loads(args.candidate.read_text(encoding="utf-8")),
    )
    if args.output_prefix:
        write_outputs(result, args.output_prefix)
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["status"] in {"feasible", "underdetermined"} else 3


if __name__ == "__main__":
    raise SystemExit(main())
