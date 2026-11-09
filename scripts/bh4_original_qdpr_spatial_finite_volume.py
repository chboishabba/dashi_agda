#!/usr/bin/env python3
"""ONE physically source-identified finite-volume BH4 chemical system.

Source chemistry:
  RHEA:32253 / Reactome R-HSA-71130.5 / human cytosol:
  (6R)-L-erythro-6,7-dihydrobiopterin + NADH + H+
     -> (6R)-L-erythro-tetrahydrobiopterin + NAD+.

Physics:
  One shared 27-voxel 3x3x3 material inventory containing the five
  *specific* original ChEBI species. Source-qualified cytosolic
  reaction events change species counts by the original stoichiometric
  column, and directed transport events debit and credit the same
  shared voxel state. Source-verified molecular atom and electric
  charge invariants hold for every selected internal event.
  External additions/removals must separately enter the balance.

This is a conservative integer-event physical candidate, NOT an
in-vivo patient flux, diffusion/PNP solution, measured permeability,
original specimen assay or clinical/mechanistic Kitzerow validation.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from dataclasses import dataclass
from itertools import product

RHEA = "RHEA:32253"
REACTOME = "R-HSA-71130.5"
C = {
    "CHEBI:43120": ((9, 13, 5, 3, 0), 0, "qDHB"),
    "CHEBI:57945": ((21, 27, 7, 14, 2), -2, "NADH"),
    "CHEBI:15378": ((0, 1, 0, 0, 0), +1, "H+"),
    "CHEBI:59560": ((9, 15, 5, 3, 0), 0, "BH4"),
    "CHEBI:57540": ((21, 26, 7, 14, 2), -1, "NAD+"),
}
INPUT = ("CHEBI:43120", "CHEBI:57945", "CHEBI:15378")
OUTPUT = ("CHEBI:59560", "CHEBI:57540")
POINTS = tuple(product(range(3), repeat=3))
POINT_SET = set(POINTS)
BONDS = tuple(
    (p, tuple(p[i] + int(i == axis) for i in range(3)))
    for p in POINTS for axis in range(3) if p[axis] < 2
)
BOND_SET = set(BONDS)
assert len(POINTS) == 27 and len(BONDS) == 54
TRANSPORT_MODES = ("local", "vascular", "plasma_membrane", "interstitial", "blood_brain_barrier")


def point(value):
    if not isinstance(value, (list, tuple)) or tuple(value) not in POINT_SET:
        raise ValueError("original 3x3x3 site is required")
    return tuple(value)


def count(value):
    if type(value) is not int or value < 0:
        raise ValueError("original discrete amount must be nonnegative integer")
    return value


def composition(items):
    return (
        tuple(sum(C[item][0][i] for item in items) for i in range(5)),
        sum(C[item][1] for item in items)
    )


@dataclass(frozen=True)
class QDPR:
    site: tuple
    number: int
    source_rhea: str
    source_reactome: str


@dataclass(frozen=True)
class Flow:
    origin: tuple
    target: tuple
    species: str
    number: int
    mode: str
    permitted: bool
    source_reference: str


@dataclass(frozen=True)
class Boundary:
    site: tuple
    species: str
    number: int
    incoming: bool
    source_reference: str


def empty():
    return {(p, chem): 0 for p in POINTS for chem in C}


def totals(state):
    if set(state) != set(empty()):
        raise ValueError("original complete 27x5 spatial species inventory required")
    atoms = tuple(
        sum(count(n) * C[chem][0][k] for (_, chem), n in state.items())
        for k in range(5)
    )
    charge = sum(count(n) * C[chem][1] for (_, chem), n in state.items())
    return atoms, charge


def plus(tot_a, tot_b):
    a, qa = tot_a
    b, qb = tot_b
    return tuple(a[i] + b[i] for i in range(5)), qa + qb


def mult(species, n):
    a, q, _ = C[species]
    return tuple(n * a[i] for i in range(5)), n*q


def transition(state, actions, *, cell_compartments):
    if set(state) != set(empty()):
        raise ValueError("source shared spatial state lacks original species/sites")
    if set(cell_compartments) != POINT_SET:
        raise ValueError("compartment assignment required for every voxel")
    state = state.copy()
    at_start = totals(state)
    boundary_inputs = ((0,)*5, 0)
    boundary_outputs = ((0,)*5, 0)
    n_reactions = 0
    n_internal_transfers = 0
    for event in actions:
        before = totals(state)
        if isinstance(event, QDPR):
            pos = point(event.site)
            n = count(event.number)
            if cell_compartments[pos] != "cytosol":
                raise ValueError("human Reactome original QDPR context is cytosol")
            if (event.source_rhea, event.source_reactome) != (RHEA, REACTOME):
                raise ValueError("unverified source reaction identity")
            if composition(INPUT) != composition(OUTPUT):
                raise AssertionError("source-specific Rhea chemistry mismatch")
            if any(state[pos, chem] < n for chem in INPUT):
                raise ValueError("original QDPR reactants absent")
            for chem in INPUT:
                state[pos, chem] -= n
            for chem in OUTPUT:
                state[pos, chem] += n
            n_reactions += n
        elif isinstance(event, Flow):
            src, dst = point(event.origin), point(event.target)
            n = count(event.number)
            if src == dst or event.species not in C or event.mode not in TRANSPORT_MODES:
                raise ValueError("invalid original chemical transport")
            if event.mode == "local" and (src, dst) not in BOND_SET and (dst, src) not in BOND_SET:
                raise ValueError("fictional native lattice connection")
            if not event.source_reference.strip() or (n and not event.permitted):
                raise ValueError("source-unpaid or physically blocked transport")
            if state[src, event.species] < n:
                raise ValueError("source compartment lacks requested material")
            state[src, event.species] -= n
            state[dst, event.species] += n
            n_internal_transfers += n
        elif isinstance(event, Boundary):
            pos = point(event.site)
            n = count(event.number)
            if event.species not in C or type(event.incoming) is not bool:
                raise ValueError("untyped external boundary event")
            if not event.source_reference.strip():
                raise ValueError("source-unpaid environmental exchange")
            if event.incoming:
                state[pos, event.species] += n
                boundary_inputs = plus(boundary_inputs, mult(event.species, n))
            else:
                if state[pos, event.species] < n:
                    raise ValueError("environmental overdraw")
                state[pos, event.species] -= n
                boundary_outputs = plus(boundary_outputs, mult(event.species, n))
        else:
            raise ValueError("unrecognized original spatial-chemistry event")
        after = totals(state)
        if isinstance(event, (Flow, QDPR)) and before != after:
            raise AssertionError("internal chemistry/transport violated original atom/charge balance")
    after = totals(state)
    if plus(after, boundary_outputs) != plus(at_start, boundary_inputs):
        raise AssertionError("full open-system source/exchange conservation failed")
    return state, {
        "source_rhea": RHEA, "source_reactome": REACTOME,
        "source_compartment": "human cytosol",
        "initial_atoms_and_charge": at_start,
        "final_atoms_and_charge": after,
        "environmental_inputs_atoms_and_charge": boundary_inputs,
        "environmental_outputs_atoms_and_charge": boundary_outputs,
        "original_QDPR_events": n_reactions,
        "internally_transported_species_quanta": n_internal_transfers,
        "exact_CHNOP_and_signed_charge_balance": True,
        "physiological_rate_measured": False,
        "transport_permeability_source_paid": False,
        "experiment_independently_validated": False,
    }


def self_test():
    assert composition(INPUT) == composition(OUTPUT) == ((30, 41, 12, 17, 2), -1)
    source, target = (0, 0, 0), (1, 0, 0)
    compartments = {p: "cytosol" for p in POINTS}
    compartments[(2, 2, 2)] = "plasma"
    state = empty()
    for chem in INPUT:
        state[source, chem] = 2

    # A REAL source-identified balanced molecular reaction and a SYNTHETIC
    # one-step transport followed by a target-local cofactor readout.
    events = (
        QDPR(source, 1, RHEA, REACTOME),
        Flow(source, target, "CHEBI:59560", 1, "local", True,
             "synthetic-admitted-native-bond-not-physiology"),
    )
    out, receipt = transition(state, events, cell_compartments=compartments)
    assert out[target, "CHEBI:59560"] == 1
    assert out[source, "CHEBI:59560"] == 0
    assert out[source, "CHEBI:43120"] == 1
    assert receipt["original_QDPR_events"] == 1
    assert receipt["internally_transported_species_quanta"] == 1
    assert receipt["initial_atoms_and_charge"] == receipt["final_atoms_and_charge"]

    # Every one of the 54 original bonds, either orientation and all 5
    # original ChEBI species: a shared state and exact molecular balances.
    checks = 0
    for origin, target in BONDS:
        for first, second in ((origin, target), (target, origin)):
            for chem in C:
                one = empty()
                one[first, chem] = 1
                after, proof = transition(
                    one,
                    (Flow(first, second, chem, 1, "local", True, "synthetic-native-grid"),),
                    cell_compartments=compartments,
                )
                assert after[second, chem] == 1
                assert proof["initial_atoms_and_charge"] == proof["final_atoms_and_charge"]
                checks += 1

    def rejects(action):
        try:
            transition(state, (action,), cell_compartments=compartments)
        except ValueError:
            return
        raise AssertionError("invalid original-source spatial event passed")

    rejects(QDPR((2, 2, 2), 1, RHEA, REACTOME))
    rejects(QDPR(source, 1, "RHEA:17869", REACTOME))
    rejects(QDPR(source, 1, RHEA, "R-HSA-OTHER"))
    rejects(QDPR(source, 3, RHEA, REACTOME))
    rejects(Flow(source, (2, 2, 2), "CHEBI:59560", 1, "local", True, "fake-neighbour"))
    rejects(Flow(source, target, "CHEBI:59560", 1, "local", False, "blocked"))
    rejects(Boundary(target, "CHEBI:59560", 1, False, "source-unpaid-value"))

    print(json.dumps({
        "status": "passed-original-Rhea-chemistry-synthetic-spatial-event-rate",
        "source_reaction": RHEA,
        "source_reactome": REACTOME,
        "original_species_count": len(C),
        "native_sites": len(POINTS),
        "original_positive_bonds": len(BONDS),
        "single-bond-oriented-species-checks": checks,
        "source_stoichiometric_CHNOP_net_charge": composition(INPUT),
        "selected_local_product_after_QDPR_and_transfer": 1,
        "kinetics_measured": False,
        "physical_transfer_rate_verified": False,
        "Agda_kernel_accepted": False,
    }, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    # No external calibrated dataset is accepted by this fixture yet.
    # Default operation is the same explicitly synthetic self-test so the
    # existing source-regression aggregate can run it via runpy.run_path.
    self_test()
