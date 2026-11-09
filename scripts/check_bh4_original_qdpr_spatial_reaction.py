#!/usr/bin/env python3
"""Original RHEA:32253 single-compartment QDPR reaction in a spatial event ledger.

RHEA:32253: q-6,7-DHB + NADH + H(+) -> BH4 + NAD(+).
Original chemistry (C,H,N,O,P and charge) is independently identified by
Rhea and Reactome's HUMAN CYTOSOL R-HSA-71130.5; the event count is a
synthetic integer stoichiometric instance, not a kinetic or clinical rate.

Do not collapse q-dihydrobiopterin into any generic "BH2" pool or equate
a plasma concentration with a cytosolic BH4 amount.
"""
from __future__ import annotations

import json
from dataclasses import dataclass

SPECIES = {
    "CHEBI:43120": {"name": "q-dihydrobiopterin", "formula": (9, 13, 5, 3, 0), "charge": 0},
    "CHEBI:57945": {"name": "NADH", "formula": (21, 27, 7, 14, 2), "charge": -2},
    "CHEBI:15378": {"name": "proton", "formula": (0, 1, 0, 0, 0), "charge": 1},
    "CHEBI:59560": {"name": "BH4", "formula": (9, 15, 5, 3, 0), "charge": 0},
    "CHEBI:57540": {"name": "NAD+", "formula": (21, 26, 7, 14, 2), "charge": -1},
}
REACTANTS = ("CHEBI:43120", "CHEBI:57945", "CHEBI:15378")
PRODUCTS = ("CHEBI:59560", "CHEBI:57540")
RHEA = "RHEA:32253"
REACTOME = "R-HSA-71130.5"


def formula(species):
    return tuple(sum(SPECIES[s]["formula"][i] for s in species)
                 for i in range(5))


def charge(species):
    return sum(SPECIES[s]["charge"] for s in species)


def initial():
    return {
        (site, chem): 0
        for site in ("plasma", "human-cytosol")
        for chem in SPECIES
    }


def original_qdpr_event(state, *, compartment, events, source_rhea, source_reactome):
    if compartment != "human-cytosol":
        raise ValueError("source Reactome specifies cytosol but does not establish endothelial cell identity")
    if (source_rhea, source_reactome) != (RHEA, REACTOME):
        raise ValueError("source reaction crosswalk not established")
    if type(events) is not int or events < 0:
        raise ValueError("integer nonnegative reaction-count witness required")
    if formula(REACTANTS) != formula(PRODUCTS) or charge(REACTANTS) != charge(PRODUCTS):
        raise ValueError("original Rhea chemistry is not balanced")
    current = state.copy()
    for species in REACTANTS:
        if current[compartment, species] < events:
            raise ValueError("insufficient original cytosolic QDPR substrate")
    for species in REACTANTS:
        current[compartment, species] -= events
    for species in PRODUCTS:
        current[compartment, species] += events
    before_formula = tuple(sum(
        state[site, species] * SPECIES[species]["formula"][i]
        for site in ("plasma", "human-cytosol")
        for species in SPECIES) for i in range(5))
    after_formula = tuple(sum(
        current[site, species] * SPECIES[species]["formula"][i]
        for site in ("plasma", "human-cytosol")
        for species in SPECIES) for i in range(5))
    before_charge = sum(
        state[site, species] * SPECIES[species]["charge"]
        for site in ("plasma", "human-cytosol")
        for species in SPECIES)
    after_charge = sum(
        current[site, species] * SPECIES[species]["charge"]
        for site in ("plasma", "human-cytosol")
        for species in SPECIES)
    if before_formula != after_formula or before_charge != after_charge:
        raise AssertionError("source-specific reaction changed atoms or net charge")
    return current


def self_test():
    assert formula(REACTANTS) == formula(PRODUCTS) == (30, 41, 12, 17, 2)
    assert charge(REACTANTS) == charge(PRODUCTS) == -1
    s = initial()
    for chem in REACTANTS:
        s["human-cytosol", chem] = 3
    original = s.copy()
    after = original_qdpr_event(
        s, compartment="human-cytosol", events=2,
        source_rhea=RHEA, source_reactome=REACTOME)
    assert after["human-cytosol", "CHEBI:59560"] == 2
    assert after["human-cytosol", "CHEBI:43120"] == 1
    assert after["plasma", "CHEBI:59560"] == 0
    assert original["human-cytosol", "CHEBI:59560"] == 0
    for invalid in (
        dict(compartment="plasma", events=1, source_rhea=RHEA, source_reactome=REACTOME),
        dict(compartment="human-cytosol", events=4, source_rhea=RHEA, source_reactome=REACTOME),
        dict(compartment="human-cytosol", events=1, source_rhea="RHEA:17869", source_reactome=REACTOME),
        dict(compartment="human-cytosol", events=1, source_rhea=RHEA, source_reactome="other"),
    ):
        try:
            original_qdpr_event(s, **invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid QDPR physical-context evidence admitted")
    print(json.dumps({
        "status": "passed-original-stoichiometry-synthetic-event-count",
        "rhea": RHEA, "reactome": REACTOME,
        "compartment": "cytosol-model-context",
        "reactant_element_inventory": list(formula(REACTANTS)),
        "product_element_inventory": list(formula(PRODUCTS)),
        "net_charge_reactants_and_products": charge(REACTANTS),
        "events_tested": 2,
        "plasma_pool_automatically_equal_to_cytosol": False,
        "kinetic_flux_measured": False,
        "transport_to_other_compartments_proven": False,
    }, indent=2))


if __name__ == "__main__":
    self_test()
