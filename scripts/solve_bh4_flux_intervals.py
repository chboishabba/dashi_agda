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
import math
from pathlib import Path


def parameter_map(parameters: dict) -> dict[str, dict]:
    return {str(row.get("parameter_id")): row for row in parameters.get("parameters", []) if row.get("parameter_id")}


def paid_bound(row: dict | None) -> tuple[float, float] | None:
    if not isinstance(row, dict) or row.get("payment_status") not in (
        "measured", "derived", "bounded-literature"
    ) or row.get("usable_for_joint_flux_witness") is not True:
        return None
    if not all(row.get(key) for key in (
        "source_reference", "same_object_reference",
        "compartment_reference", "measurement_time_reference"
    )) or not isinstance(row.get("unit"), str) or not row["unit"].strip():
        return None
    try:
        lower, upper = float(row["lower"]), float(row["upper"])
    except (TypeError, ValueError, OverflowError):
        return None
    if not math.isfinite(lower) or not math.isfinite(upper) or lower > upper:
        return None
    return lower, upper


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
    source_rows = parameter_receipt.get("parameters", [])
    if not isinstance(source_rows, list) or any(
        not isinstance(row, dict) for row in source_rows
    ):
        return {
            "schema": "dashi.bh4-interval-flux-solver.v1",
            "status": "underdetermined",
            "reason": "parameter manifest malformed",
            "candidate_flux_balance_witness": None,
            "promotion_boundary": promotion_boundary(),
        }
    ids = [str(row.get("parameter_id")) for row in source_rows if row.get("parameter_id")]
    if len(ids) != len(set(ids)):
        return {
            "schema": "dashi.bh4-interval-flux-solver.v1",
            "status": "underdetermined",
            "reason": "duplicate parameter coordinates",
            "candidate_flux_balance_witness": None,
            "promotion_boundary": promotion_boundary(),
        }
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
    if len(units) != 1 or units[0] in ("None", "", "nan", "unknown"):
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
        # SciPy/HiGHS provides a floating-point candidate, not a
        # mathematical exact-equality certificate or laboratory receipt.
        # Check its returned vector against the input intervals and S*v+e
        # separately. An unchecked solver success never creates a witness.
        x_values = [float(value) for value in result.x]
        max_balance_residual = max(
            [abs(sum(float(matrix[i][j]) * x_values[j]
                     for j in range(n_r)) + x_values[n_r + i])
             for i in range(len(species))] or [0.0]
        )
        max_bound_violation = max(
            [max(lower - value, value - upper, 0.0)
             for value, (lower, upper) in zip(x_values, bounds)] or [0.0]
        )
        tolerance = 1e-7 * max(
            1.0, max((abs(x) for x in x_values), default=0.0)
        )
        numerically_checked = (
            all(math.isfinite(x) for x in x_values)
            and math.isfinite(max_balance_residual)
            and math.isfinite(max_bound_violation)
            and max_balance_residual <= tolerance
            and max_bound_violation <= tolerance
        )
        if not numerically_checked:
            return {
                "schema": "dashi.bh4-interval-flux-solver.v1",
                "status": "underdetermined",
                "reason": "solver candidate failed independent finite residual/bound check",
                "candidate_flux_balance_witness": None,
                "postcheck_tolerance": tolerance,
                "max_balance_residual": max_balance_residual,
                "max_bound_violation": max_bound_violation,
                "promotion_boundary": promotion_boundary(),
            }
        witness = {
            "postcheck_max_balance_residual": max_balance_residual,
            "postcheck_max_bound_violation": max_bound_violation,
            "postcheck_tolerance": tolerance,
            "numeric_candidate_only": True,
            "original_source_receipts_independently_authenticated": False,
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
