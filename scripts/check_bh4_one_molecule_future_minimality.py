#!/usr/bin/env python3
"""Independent exhaustive one-molecule future-equivalence acceptance test.

Physical finite slice: source BH4, target BH4, target oxidized pool.
All four actions are transported to the *same original three-coordinate*
shared-state physical update. Only a selected target-oxidation readout
is observed, so the formal result identifies the exact minimal
intervention-safe partition for that declared observation language.
Original molecular redox kinetics and biological phenotype NOT claimed.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json

OWNER = Path(__file__).resolve().parents[1] / (
    "DASHI/Biology/BH4OneMoleculeSpatialFutureMinimalityExact.agda"
)
STATES = ("sourceReduced", "targetReduced", "targetOxidized")
ACTIONS = ("hold", "deliverToTarget", "oxidizeAtTarget", "recycleAtTarget")
ENCODE = {"sourceReduced": (1, 0, 0), "targetReduced": (0, 1, 0), "targetOxidized": (0, 0, 1)}
PHYSICAL = {"hold": "gateClosed", "deliverToTarget": "deliver",
            "oxidizeAtTarget": "oxidize", "recycleAtTarget": "recycle"}


def step(action, state):
    if action == "deliverToTarget" and state == "sourceReduced":
        return "targetReduced"
    if action == "oxidizeAtTarget" and state == "targetReduced":
        return "targetOxidized"
    if action == "recycleAtTarget" and state == "targetOxidized":
        return "targetReduced"
    return state


def physical_step(action, state):
    a, b, c = state
    if action == "deliver" and a:
        return (a-1, b+1, c)
    if action == "oxidize" and b:
        return (a, b-1, c+1)
    if action == "recycle" and c:
        return (a, b+1, c-1)
    return state


def readout(state):
    return int(state == "targetOxidized")


def run(state, word):
    for action in word:
        assert ENCODE[step(action, state)] == physical_step(PHYSICAL[action], ENCODE[state])
        state = step(action, state)
    return state


def main():
    content = OWNER.read_text()
    for lemma in (
        "selectedOriginalPhysicalStepCommutes",
        "futureEquivalentImpliesIdenticalPhysicalState",
        "identicalPhysicalStateImpliesFutureEquivalent",
        "allSelectedPhysicalMoietiesEqualOne",
        "globalMoietyCountCannotPredictAllSelectedFutures",
    ):
        assert lemma in content, f"Agda source owner missing: {lemma}"

    # Exact Myhill-Nerode-style future signatures up to length 6 are
    # sufficient to distinguish all 3 states in this selected model.
    words = ((),) + tuple(
        word for length in range(1, 7)
        for word in product(ACTIONS, repeat=length)
    )
    assert all(sum(ENCODE[state]) == 1 for state in STATES)
    signatures = {}
    for state in STATES:
        signatures[state] = tuple(readout(run(state, word)) for word in words)
    assert len(set(signatures.values())) == 3
    assert signatures["sourceReduced"][0] == signatures["targetReduced"][0] == 0
    assert signatures["targetOxidized"][0] == 1
    assert readout(run("sourceReduced", ("oxidizeAtTarget",))) == 0
    assert readout(run("targetReduced", ("oxidizeAtTarget",))) == 1
    assert all(
        ENCODE[step(a, s)] == physical_step(PHYSICAL[a], ENCODE[s])
        for s in STATES for a in ACTIONS
    )
    print(json.dumps({
        "status": "passed-synthetic-physical-future-partition",
        "physical_one_molecule_states": len(STATES),
        "global_biopterin_moieties_each": 1,
        "selected_controls": list(ACTIONS),
        "observation": "target-oxidized-pterin-present",
        "future_words_enumerated_per_state": len(words),
        "minimal_distinct_future_classes": len(set(signatures.values())),
        "finite_redox_transition_projection_commutes": True,
        "source_specific_in_vivo_kinetics_paid": False,
        "Agda_kernel_acceptance": False
    }, indent=2))


if __name__ == "__main__":
    main()
