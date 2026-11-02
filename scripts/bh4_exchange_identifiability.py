#!/usr/bin/env python3
"""Exact integer diagnostic for the already known free-exchange non-identifiability.

Given any integer stoichiometric matrix and integer reaction vector v,
e=-S*v exactly balances S*v+e. Never use that synthetically determined
exchange vector as source-paid transport, a physiological observation
or evidence for Kitzerow's proposed simultaneous-demand mechanism.
"""
from __future__ import annotations

from typing import Any


def _integer_matrix(matrix: dict[str, Any]) -> tuple[list[str], list[str], list[list[int]]]:
    if matrix.get("schema") != "dashi.bh4-stoichiometric-matrix.v1":
        raise ValueError("unexpected matrix ABI")
    reactions = matrix.get("reaction_index")
    species = matrix.get("species_index")
    values = matrix.get("matrix")
    if not isinstance(reactions, list) or not isinstance(species, list) or not isinstance(values, list):
        raise ValueError("matrix carrier incomplete")
    if (not reactions or not species or len(reactions) != len(set(reactions))
            or len(species) != len(set(species)) or len(values) != len(species)
            or any(not isinstance(row, list) or len(row) != len(reactions) or
                   any(type(x) is not int for x in row) for row in values)):
        raise ValueError("matrix dimensions or exact coefficient certification invalid")
    return reactions, species, values


def synthetic_unrestricted_exchange(matrix: dict, reaction_flux: dict[str, int]) -> dict:
    """Return a pure algebraic witness with explicit nonphysical provenance."""
    reactions, species, values = _integer_matrix(matrix)
    if not isinstance(reaction_flux, dict) or set(reaction_flux) != set(reactions):
        raise ValueError("reaction vector does not match finite reaction set")
    if any(type(reaction_flux[rid]) is not int for rid in reactions):
        raise ValueError("reaction flux must be exact integers for this diagnostic")
    v = [reaction_flux[r] for r in reactions]
    sv = [sum(row[j] * v[j] for j in range(len(v))) for row in values]
    e = [-x for x in sv]
    assert all(sum(row[j] * v[j] for j in range(len(v))) + e[i] == 0
               for i, row in enumerate(values))
    return {
        "schema": "dashi.bh4-free-exchange-identity.v1",
        "reaction_variables": len(reactions),
        "exchange_variables": len(species),
        "reaction_flux": {r: reaction_flux[r] for r in reactions},
        "algebraic_internal_increment": {s: sv[i] for i, s in enumerate(species)},
        "synthetic_exchange": {s: e[i] for i, s in enumerate(species)},
        "exact_integer_balance_residual": 0,
        "exchange_bounds_paid": False,
        "reaction_bounds_paid": False,
        "source_supports_this_flux": False,
        "same_compartment_and_time_verified": False,
        "simultaneous_BH4_demands_tested": False,
        "clinical_claim_tested": False,
        "usable_for_joint_flux_witness": False,
        "classification": "algebraic-non-identifiability-only",
    }


def check_exchange_bounds(candidate: dict, exchange_bounds: dict[str, tuple[int, int]]) -> dict:
    """Separate the new *assumption* of exchange limits from exact balancing."""
    if candidate.get("schema") != "dashi.bh4-free-exchange-identity.v1":
        raise ValueError("not an algebraic free-exchange witness")
    e = candidate["synthetic_exchange"]
    if not isinstance(exchange_bounds, dict) or set(exchange_bounds) != set(e):
        raise ValueError("all exchange coordinates must be explicitly constrained")
    violated = []
    for species in sorted(e):
        limits = exchange_bounds[species]
        if (not isinstance(limits, (tuple, list)) or len(limits) != 2
                or any(type(x) is not int for x in limits) or limits[0] > limits[1]):
            raise ValueError("invalid exact integer bounds")
        if not limits[0] <= e[species] <= limits[1]:
            violated.append(species)
    return {
        "schema": "dashi.bh4-free-exchange-assumption-test.v1",
        "candidate_within_supplied_bounds": not violated,
        "violating_species": violated,
        "bounds_source_paid": False,
        "synthetic_candidate_global_feasibility": False,
        "claim": "one candidate tested against caller-supplied assumptions; not all possible reaction vectors",
    }
