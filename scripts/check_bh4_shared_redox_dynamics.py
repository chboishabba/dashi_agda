#!/usr/bin/env python3
"""Exhaustive exact-integer reference semantics for original BH4 shared
source/target reduction/oxidation Agda proof owner. Synthetic only.

Every action operates on ONE shared state (sourceBH4,targetBH4,targetBH2)
and time ordering is causal. No kinetic law, full Rhea stoichiometry,
redox electron/oxygen conservation, transport calibration or clinical
claim is supplied.
"""
from __future__ import annotations
import itertools
from pathlib import Path
import json

OWNER = (Path(__file__).resolve().parents[1] /
         "DASHI/Biology/BH4SharedSourceTargetRedoxDynamicsExact.agda")

ACTIONS = ("gateClosed", "deliver", "oxidize", "recycle", "inject2")

def step(action, state):
    a, b, c = state
    if action == "gateClosed":
        return state, 0
    if action == "deliver":
        return (a-1, b+1, c) if a else state, 0
    if action == "oxidize":
        return (a, b-1, c+1) if b else state, 0
    if action == "recycle":
        return (a, b+1, c-1) if c else state, 0
    if action == "inject2":
        return (a+2, b, c), 2
    raise ValueError(action)

def run(actions, initial):
    current = initial
    supplied = 0
    for action in actions:
        before = sum(current)
        current, injected = step(action, current)
        assert min(current) >= 0
        assert sum(current) == before + injected
        supplied += injected
    assert sum(current) == sum(initial) + supplied
    return current, supplied

def main():
    original = OWNER.read_text()
    for theorem in (
        "deliveryConservesBiopterin", "oxidationConservesBiopterin",
        "recyclingConservesBiopterin", "oneStepOpenSystemBalance",
        "allControlledHistoriesPreserveOpenBiopterinBalance",
        "deliveryAndOxidationDoNotCommute",
    ):
        assert theorem in original, f"missing Agda proof owner {theorem}"

    initial = (1, 0, 0)
    assert run(("deliver", "oxidize"), initial)[0] == (0, 0, 1)
    assert run(("oxidize", "deliver"), initial)[0] == (0, 1, 0)
    assert run(("deliver", "oxidize", "recycle"), initial)[0] == (0, 1, 0)

    examples = 0
    # Every three-coordinate inventory up to 4, every controlled event word
    # of length 0..4, with explicit repeated open-system supply.
    for state in itertools.product(range(5), repeat=3):
        for n in range(5):
            for word in itertools.product(ACTIONS, repeat=n):
                run(word, state)
                examples += 1

    print(json.dumps({
        "status": "passed-synthetic-integer-semantics",
        "initial_states": 125,
        "actions": list(ACTIONS),
        "history_horizon_exhaustive_through": 4,
        "conserved_histories_tested": examples,
        "noncommuting_deliver_oxidize": True,
        "same_target_redox_inventory": True,
        "original_reaction_electron_balance_paid": False,
        "original_tissue_flux_calibrated": False,
        "agda_kernel_receipt": False,
    }, indent=2))

if __name__ == "__main__":
    main()
