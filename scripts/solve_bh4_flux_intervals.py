#!/usr/bin/env python3
"""Search for a bounded steady-state BH4 flux witness with linear programming.

Variables are the executed reaction fluxes v followed by one external exchange
coordinate e for every finite species. Positive exchange adds material to the
modeled system. The feasibility problem is

    S*v + e = 0

subject to source-paid lower/upper bounds from the Phase-4 parameter manifest.
Every `REACTION_FLUX:<RHEA-ID>` and `EXCHANGE:<species-id>` row must be marked
usable_for_joint_flux_witness. Missing coordinates yield `underdetermined`;
they are never replaced with zero or unbounded intervals.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def parameter_map(parameters: dict) -> dict[str, dict]:
    return {str(row.get("parameter_id")): row for row in parameters.get("parameters", []) if row.get("parameter_id")}


def paid_bound(row: dict | None) -> tuple[float, float] | None:
    if not row or row.get("payment_status") == "unresolved" or not row.get("usable_for_joint_flux_witness"):
        return None
    if row.get("lower") is None or row.get("upper") is None:
        return None
    return float(row["lower"]), float(row["upper"])


def promotion_boundary() -> dict:
    return {
        "missing_reaction_bound_substituted_with_zero": False,
        "missing_exchange_bound_substituted_with_zero": False,
        "kinetic_constant_automatically_promoted_to_flux_bound": False,
        "feasible_steady_state_proves_allocator_causality": False,
        "feasible_steady_state_proves_disease_mechanism": False,
        "steady_state_infeasible_proves_all_dynamic_states_impossible": False,
    }


def solve(matrix_receipt: dict, parameter_receipt: dict) -> dict:
    reactions = list(matrix_receipt.get("reaction_index", []))
    species = list(matrix_receipt.get("species_index", []))
    matrix = matrix_receipt.get("matrix", [])
    pmap = parameter_map(parameter_receipt)

    if len(matrix) != len(species) or any(len(row) != len(reactions) for row in matrix):
        return {"schema": "dashi.bh4-interval-flux-solver.v1", "status": "underdetermined", "reason": "invalid matrix dimensions", "promotion_boundary": promotion_boundary()}

    reaction_rows = [(rid, pmap.get(f"REACTION_FLUX:{rid}")) for rid in reactions]
    exchange_rows = [(sid, pmap.get(f"EXCHANGE:{sid}")) for sid in species]
    missing_reaction = [rid for rid, row in reaction_rows if paid_bound(row) is None]
    missing_exchange = [sid for sid, row in exchange_rows if paid_bound(row) is None]

    if missing_reaction or missing_exchange:
        return {
            "schema": "dashi.bh4-interval-flux-solver.v1",
            "status": "underdetermined",
            "reaction_variables": len(reactions),
            "exchange_variables": len(species),
            "missing_reaction_bounds": missing_reaction,
            "missing_exchange_bounds": missing_exchange,
            "candidate_flux_balance_witness": None,
            "promotion_boundary": promotion_boundary(),
        }

    solver_rows = [row for _, row in reaction_rows + exchange_rows]
    units = sorted({str(row.get("unit")) for row in solver_rows})
    if len(units) != 1:
        return {
            "schema": "dashi.bh4-interval-flux-solver.v1",
            "status": "underdetermined",
            "reason": "solver coordinates do not share one normalized flux unit",
            "units": units,
            "candidate_flux_balance_witness": None,
            "promotion_boundary": promotion_boundary(),
        }

    try:
        from scipy.optimize import linprog
    except ImportError:
        return {
            "schema": "dashi.bh4-interval-flux-solver.v1",
            "status": "solver-unavailable",
            "reason": "scipy.optimize.linprog is not installed",
            "candidate_flux_balance_witness": None,
            "promotion_boundary": promotion_boundary(),
        }

    bounds = [paid_bound(row) for _, row in reaction_rows] + [paid_bound(row) for _, row in exchange_rows]
    n_r = len(reactions)
    a_eq = []
    for i, row in enumerate(matrix):
        a_eq.append([float(x) for x in row] + [1.0 if i == j else 0.0 for j in range(len(species))])

    result = linprog(
        c=[0.0] * (n_r + len(species)),
        A_eq=a_eq,
        b_eq=[0.0] * len(species),
        bounds=bounds,
        method="highs",
    )

    if result.success:
        flux = {rid: float(result.x[j]) for j, rid in enumerate(reactions)}
        exchange = {sid: float(result.x[n_r + i]) for i, sid in enumerate(species)}
        status = "feasible"
        witness = {
            "reaction_flux": flux,
            "external_exchange": exchange,
            "normalized_flux_unit": units[0],
            "max_equality_residual": float(max(abs(x) for x in result.eqlin.residual)) if len(result.eqlin.residual) else 0.0,
            "solver": "scipy.optimize.linprog(method=highs)",
        }
    elif result.status == 2:
        status = "infeasible"
        witness = None
    else:
        status = "underdetermined"
        witness = None

    return {
        "schema": "dashi.bh4-interval-flux-solver.v1",
        "status": status,
        "reaction_variables": len(reactions),
        "exchange_variables": len(species),
        "normalized_flux_unit": units[0],
        "solver_status": int(result.status),
        "solver_message": str(result.message),
        "candidate_flux_balance_witness": witness,
        "promotion_boundary": promotion_boundary(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--parameters", type=Path, required=True)
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    payload = solve(
        json.loads(args.matrix.read_text(encoding="utf-8")),
        json.loads(args.parameters.read_text(encoding="utf-8")),
    )
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 3 if payload["status"] == "infeasible" else 0


if __name__ == "__main__":
    raise SystemExit(main())
