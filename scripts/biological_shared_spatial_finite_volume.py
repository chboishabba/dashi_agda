#!/usr/bin/env python3
"""One shared 27-voxel source-indexed open biopterin reaction/transport system.

PHYSICAL STATUS: exact finite-volume *candidate* model, NOT source-calibrated
biological kinetics. Internal directed transfers debit one original shared
voxel inventory and credit another. Explicit BH4<->BH2 redox conversions
preserve the total biopterin moiety; external supply/clearance alone change
that total. Vascular links are independent from the 54 native local bonds.

No floating point, inferred circulation rates, patient diagnosis, or claims
of a measured planar/regenerative BH4 model.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path

VOXELS = tuple(product(range(3), repeat=3))
VOXEL_SET = set(VOXELS)
BONDS = tuple(
    (point, tuple(point[k] + int(k == axis) for k in range(3)))
    for point in VOXELS
    for axis in range(3)
    if point[axis] < 2
)
assert len(VOXELS) == 27 and len(BONDS) == 54
BOND_SET = set(BONDS)

SPECIES = ("BH4", "BH2")
CONNECTIONS = ("local", "membrane", "vascular", "interstitial", "gap_junction", "blood_brain_barrier")


def exact_integer(value):
    if type(value) is not int or value < 0:
        raise ValueError("amounts are nonnegative integer molecule quanta")
    return value


def voxel(value):
    if type(value) not in (tuple, list) or len(value) != 3:
        raise ValueError("voxel must have 3 coordinates")
    result = tuple(value)
    if result not in VOXEL_SET:
        raise ValueError("voxel outside original nonperiodic 3x3x3 geometry")
    return result


@dataclass(frozen=True)
class Transport:
    species: str
    origin: tuple[int, int, int]
    destination: tuple[int, int, int]
    amount: int
    mode: str
    source_reference: str
    permitted: bool

    def checked(self):
        if self.species not in SPECIES or self.mode not in CONNECTIONS:
            raise ValueError("unknown chemical species or transport mechanism")
        a, b = voxel(self.origin), voxel(self.destination)
        if a == b or not self.source_reference.strip():
            raise ValueError("self transfer or absent source provenance")
        if self.mode == "local" and (a, b) not in BOND_SET and (b, a) not in BOND_SET:
            raise ValueError("local transfer not a native nearest-neighbour bond")
        exact_integer(self.amount)
        if self.amount and not self.permitted:
            raise ValueError("transport across denied connection")
        return self


@dataclass(frozen=True)
class Reaction:
    voxel: tuple[int, int, int]
    substrate: str
    product: str
    amount: int
    original_reaction_reference: str

    def checked(self):
        voxel(self.voxel)
        if {self.substrate, self.product} != set(SPECIES):
            raise ValueError("selected redox-only chemistry requires BH4 and BH2")
        exact_integer(self.amount)
        if not self.original_reaction_reference.strip():
            raise ValueError("reaction provenance required")
        return self


@dataclass(frozen=True)
class Boundary:
    voxel: tuple[int, int, int]
    species: str
    amount: int
    inflow: bool
    source_reference: str

    def checked(self):
        voxel(self.voxel)
        if self.species not in SPECIES:
            raise ValueError("unknown species at boundary")
        exact_integer(self.amount)
        if type(self.inflow) is not bool or not self.source_reference.strip():
            raise ValueError("boundary direction/provenance required")
        return self


def empty_state():
    return {(site, chem): 0 for site in VOXELS for chem in SPECIES}


def total(state):
    if set(state) != set(empty_state()):
        raise ValueError("physical state has missing/extra voxel or species")
    return sum(exact_integer(q) for q in state.values())


def step(state, events):
    """Sequential event semantics. Every event sees updated shared inventory."""
    state = state.copy()
    before = total(state)
    external_in, external_out = 0, 0
    for event in events:
        event.checked()
        if isinstance(event, Transport):
            a, b = (voxel(event.origin), event.species), (voxel(event.destination), event.species)
            if state[a] < event.amount:
                raise ValueError("insufficient local inventory for transport")
            state[a] -= event.amount
            state[b] += event.amount
        elif isinstance(event, Reaction):
            a, b = (voxel(event.voxel), event.substrate), (voxel(event.voxel), event.product)
            if state[a] < event.amount:
                raise ValueError("insufficient local substrate for redox conversion")
            state[a] -= event.amount
            state[b] += event.amount
        elif isinstance(event, Boundary):
            key = (voxel(event.voxel), event.species)
            if event.inflow:
                state[key] += event.amount
                external_in += event.amount
            else:
                if state[key] < event.amount:
                    raise ValueError("external loss exceeds local inventory")
                state[key] -= event.amount
                external_out += event.amount
        else:
            raise ValueError("unknown physical event")
        total(state)
    after = total(state)
    if after + external_out != before + external_in:
        raise AssertionError("physical open-system moiety balance violated")
    return state, {"before": before, "after": after,
                   "injected": external_in, "removed": external_out,
                   "balance_residual": after + external_out - before - external_in}


def self_test():
    first, second, third = (0, 0, 0), (1, 0, 0), (2, 2, 2)
    initial = empty_state()
    initial[first, "BH4"] = 5
    original = initial.copy()
    synthetic = "synthetic-not-measured"
    events = [
        Transport("BH4", first, second, 3, "local", synthetic, True),
        Reaction(second, "BH4", "BH2", 1, "synthetic-QDPR-reversible-redox",),
        Transport("BH2", second, third, 1, "vascular", synthetic, True),
        Boundary(third, "BH2", 2, True, synthetic),
        Boundary(first, "BH4", 1, False, synthetic),
    ]
    result, receipt = step(initial, events)
    assert receipt == {"before": 5, "after": 6, "injected": 2,
                       "removed": 1, "balance_residual": 0}
    assert result[second, "BH4"] == 2
    assert result[second, "BH2"] == 0
    assert result[third, "BH2"] == 3
    assert result[first, "BH4"] == 1
    assert original[first, "BH4"] == 5  # no in-place aliasing

    no_route, _ = step(initial, [])
    transported, _ = step(initial, [Transport("BH4", first, second, 1, "local", synthetic, True)])
    assert total(no_route) == total(transported)
    assert no_route[second, "BH4"] == 0
    assert transported[second, "BH4"] == 1

    # Every native local bond, both directions, and both redox species:
    # nonnegative shared state and exact one-event balance.
    verified_cases = 0
    for a, b in BONDS:
        for start, finish in ((a, b), (b, a)):
            for chem in SPECIES:
                source_state = empty_state()
                source_state[start, chem] = 1
                out, balance = step(source_state, [
                    Transport(chem, start, finish, 1, "local", synthetic, True)
                ])
                assert total(out) == 1 and balance["balance_residual"] == 0
                assert out[finish, chem] == 1
                verified_cases += 1

    for chem in SPECIES:
        other = "BH2" if chem == "BH4" else "BH4"
        for site in VOXELS:
            state = empty_state()
            state[site, chem] = 1
            output, balance = step(state, [
                Reaction(site, chem, other, 1, synthetic)
            ])
            assert total(output) == 1 and output[site, other] == 1
            assert balance["balance_residual"] == 0
            verified_cases += 1

    def fails(state, actions):
        try:
            step(state, actions)
        except ValueError:
            return
        raise AssertionError("invalid physical event admitted")

    fails(initial, [Transport("BH4", first, third, 1, "local", synthetic, True)])
    fails(initial, [Transport("BH4", first, second, 1, "local", synthetic, False)])
    fails(initial, [Transport("BH4", first, second, 6, "local", synthetic, True)])
    fails(initial, [Reaction(third, "BH4", "BH2", 1, synthetic)])
    fails(initial, [Boundary(third, "BH2", 1, False, synthetic)])
    fails(initial, [Boundary(third, "BH2", 1, True, "")])

    print(json.dumps({
        "schema": "dashi.biological.shared-27site-finite-volume.v1",
        "status": "passed-synthetic-exact-integer-candidate-only",
        "sites": len(VOXELS), "local_bonds": len(BONDS),
        "species": list(SPECIES), "single_event_checks": verified_cases,
        "open_system_test": receipt, "source_paid_physical_kinetics": False,
        "pnf_promoted": False, "agda_kernel_receipt": False
    }, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    else:
        parser.error("only --self-test is supported: no calibrated data/model shipped")


if __name__ == "__main__":
    main()
