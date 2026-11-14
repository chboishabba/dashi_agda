#!/usr/bin/env python3
"""Finite computational regression for the biology future-quotient Agda owner.

Not a proof, source measurement, calibrated biology model, or kernel receipt.
The Agda declarations remain the mathematical authority.
"""
from dataclasses import dataclass
from itertools import product
from collections import deque

ACTIONS = ("signal", "wound", "connect", "restore-memory", "provide-environment")


@dataclass(frozen=True)
class BiologicalState:
    genome: bool
    marker: bool
    memory: bool
    junction: bool
    environment: bool
    morphology: bool


def update(action: str, x: BiologicalState) -> BiologicalState:
    g, c, h, j, e, p = (
        x.genome, x.marker, x.memory, x.junction, x.environment, x.morphology
    )
    if action == "signal":
        return BiologicalState(g, c, h, j, e, g and h and j and e)
    if action == "wound":
        return BiologicalState(g, c, h, j, e, False)
    if action == "connect":
        return BiologicalState(g, c, h, True, e, p)
    if action == "restore-memory":
        return BiologicalState(g, c, True, j, e, p)
    if action == "provide-environment":
        return BiologicalState(g, c, h, j, True, p)
    raise ValueError(action)


def project(x: BiologicalState) -> tuple[bool, ...]:
    return (x.genome, x.memory, x.junction, x.environment, x.morphology)


def coarse_step(action: str, code: tuple[bool, ...]) -> tuple[bool, ...]:
    g, h, j, e, p = code
    if action == "signal":
        return (g, h, j, e, g and h and j and e)
    if action == "wound":
        return (g, h, j, e, False)
    if action == "connect":
        return (g, h, True, e, p)
    if action == "restore-memory":
        return (g, True, j, e, p)
    if action == "provide-environment":
        return (g, h, j, True, p)
    raise ValueError(action)


def all_states():
    return (BiologicalState(*v) for v in product((False, True), repeat=6))


def verify() -> None:
    states = list(all_states())
    assert len(states) == 64
    for state in states:
        for action in ACTIONS:
            assert project(update(action, state)) == coarse_step(action, project(state))
    # Finite bisimulation check: each code class follows the same coarse law.
    for x in states:
        for y in states:
            if project(x) == project(y):
                assert x.morphology == y.morphology
                for action in ACTIONS:
                    assert project(update(action, x)) == project(update(action, y))

    without = BiologicalState(True, False, False, True, True, False)
    with_memory = BiologicalState(True, False, True, True, True, False)
    different_marker = BiologicalState(True, True, False, True, True, False)
    assert without.genome == with_memory.genome
    assert without.morphology == with_memory.morphology
    assert update("signal", without).morphology is False
    assert update("signal", with_memory).morphology is True
    assert project(without) == project(different_marker) and without != different_marker

    # Exhaust traces length <=3: independent check of the structural induction.
    for depth in range(4):
        for trace in product(ACTIONS, repeat=depth):
            for state in states:
                x = state
                code = project(state)
                for action in trace:
                    x, code = update(action, x), coarse_step(action, code)
                assert project(x) == code

    # Actual nonperiodic P3 x P3 x P3 grid, 54 undirected nearest-neighbour edges.
    points = list(product((-1, 0, 1), repeat=3))
    edges = sum(
        sum(abs(a - b) for a, b in zip(x, y)) == 1
        for i, x in enumerate(points) for y in points[i + 1:]
    )
    assert len(points) == 27 and edges == 54
    print("PASS: 64 fine states, 5 local actions, traces <=3, 27-point/54-edge cube")
    print("PASS: noninjective future-safe code and memory-blind future counterexample")
    print("NO AGDA ACCEPTANCE OR EMPIRICAL CALIBRATION ASSERTED")


if __name__ == "__main__":
    verify()
