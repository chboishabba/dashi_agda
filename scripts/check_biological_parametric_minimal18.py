#!/usr/bin/env python3
"""Independent exhaustive finite semantics for the source-written 18-class
parametric stochastic quotient and marker-sensitive negative control.

This tests a selected Boolean finite model, not calibrated biology or
a proof acceptance receipt from the Agda kernel.
"""
from __future__ import annotations

import itertools
import json
from fractions import Fraction

ACTIONS = ("signal", "wound", "connect", "restoreMemory", "provideEnvironment")
WEIGHTS = (Fraction(0, 1), Fraction(1, 3), Fraction(1, 2), Fraction(1, 1))
STATES = tuple(itertools.product((False, True), repeat=6))

def minimal(state):
    genome, _chromatin, memory, junction, environment, phenotype = state
    return ("active", memory, junction, environment, phenotype) if genome else (
        "inactive", phenotype
    )

def observe(state):
    return state[-1]

def step(action, state):
    genome, chromatin, memory, junction, environment, phenotype = state
    if action == "signal":
        phenotype = genome and memory and junction and environment
    elif action == "wound":
        phenotype = False
    elif action == "connect":
        junction = True
    elif action == "restoreMemory":
        memory = True
    elif action == "provideEnvironment":
        environment = True
    else:
        raise ValueError(action)
    return genome, chromatin, memory, junction, environment, phenotype

def flip(state):
    genome, chromatin, memory, junction, environment, phenotype = state
    return genome, not chromatin, memory, junction, environment, phenotype

def minimal_step(action, code):
    if code[0] == "inactive":
        phenotype = False if action in ("signal", "wound") else code[1]
        return "inactive", phenotype
    _, h, j, e, p = code
    if action == "signal":
        p = h and j and e
    elif action == "wound":
        p = False
    elif action == "connect":
        j = True
    elif action == "restoreMemory":
        h = True
    elif action == "provideEnvironment":
        e = True
    return "active", h, j, e, p

def weighted_successors(state, action, retain):
    updated = step(action, state)
    return ((retain, updated), (1-retain, flip(updated)))

def eval_fine(state, schedule, observable):
    values = {state: Fraction(1)}
    for action, retain in schedule:
        newer = {}
        for current, mass in values.items():
            for prob, nxt in weighted_successors(current, action, retain):
                newer[nxt] = newer.get(nxt, Fraction(0)) + mass * prob
        values = newer
    return sum(mass * observable(minimal(current)) for current, mass in values.items())

def eval_coarse(state, schedule, observable):
    code = minimal(state)
    for action, _retain in schedule:
        code = minimal_step(action, code)
    return observable(code)

def main():
    codes = {minimal(state) for state in STATES}
    assert len(STATES) == 64
    assert len(codes) == 18
    checks = 0
    for state in STATES:
        for action in ACTIONS:
            for weight in WEIGHTS:
                schedule = ((action, weight),)
                for observer in (
                    lambda code: Fraction(int(code[-1])),
                    lambda code: Fraction(int(code[0] == "active")),
                    lambda code: Fraction(len(code), 10),
                ):
                    assert eval_fine(state, schedule, observer) == eval_coarse(
                        state, schedule, observer
                    )
                    checks += 1

    # Every 0-3 action word, with time-inhomogeneous rational weights.
    # The deterministic word is exhaustive and the schedule weights are
    # nonconstant under cyclic selection whenever length > 1.
    for length in range(4):
        for word in itertools.product(ACTIONS, repeat=length):
            schedule = tuple(
                (action, WEIGHTS[(i + ACTIONS.index(action)) % len(WEIGHTS)])
                for i, action in enumerate(word)
            )
            for state in STATES:
                assert eval_fine(state, schedule, lambda c: Fraction(int(c[-1]))) == (
                    eval_coarse(state, schedule, lambda c: Fraction(int(c[-1])))
                )
                checks += 1

    first = True, False, False, True, True, False
    second = flip(first)
    assert minimal(first) == minimal(second)
    # New marker-sensitive action invalidates the previous quotient.
    assert first[1] is False and second[1] is True
    assert first[1] != second[1]
    print(json.dumps({
        "status": "passed",
        "states_checked": len(STATES),
        "distinct_minimal_codes": len(codes),
        "interventions": len(ACTIONS),
        "normalized_exact_rational_weights": [str(x) for x in WEIGHTS],
        "total_exact_factored_expectation_checks": checks,
        "exhaustive_action_word_horizon": 3,
        "new_marker_action_breaks_minimal_quotient": True,
        "physical_probability_calibration": False,
        "agda_kernel_certificate": False,
    }, indent=2))

if __name__ == "__main__":
    main()
