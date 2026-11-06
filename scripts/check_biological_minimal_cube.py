#!/usr/bin/env python3
"""Exhaustive P1/P2 certificate for the explicitly finite *synthetic* fixture.

This is deliberately independent of the Agda representation.  It is not
an Agda kernel receipt, an organism-level kinetic law, or biological data.
"""
from itertools import product

ACTIONS = ("signal", "wound", "connect", "restoreMemory", "provideEnvironment")
FLAGS = (False, True)
STATES = list(product(FLAGS, repeat=6))  # g,c,h,j,e,observed morphology
WORDS = (
    (),
    ("restoreMemory", "connect", "provideEnvironment", "signal"),
    ("connect", "provideEnvironment", "signal"),
    ("restoreMemory", "provideEnvironment", "signal"),
    ("restoreMemory", "connect", "signal"),
)


def step(action, state):
    g, c, h, j, e, p = state
    if action == "signal":
        p = g and h and j and e
    elif action == "wound":
        p = False
    elif action == "connect":
        j = True
    elif action == "restoreMemory":
        h = True
    elif action == "provideEnvironment":
        e = True
    else:
        raise ValueError(action)
    return (g, c, h, j, e, p)


def run(state, actions):
    for action in actions:
        state = step(action, state)
    return state


def code(state):
    g, _c, h, j, e, p = state
    return ("active", h, j, e, p) if g else ("inactive", p)


def diagnostic(state):
    return tuple(run(state, word)[-1] for word in WORDS)


def partition(labels):
    keys = list(dict.fromkeys(labels))
    indices = {k: i for i, k in enumerate(keys)}
    return {s: indices[label] for s, label in zip(STATES, labels)}


def refine():
    classes = partition([s[-1] for s in STATES])
    sizes = [len(set(classes.values()))]
    for _ in range(20):
        updated = partition([
            (classes[s], *(classes[step(a, s)] for a in ACTIONS))
            for s in STATES
        ])
        sizes.append(len(set(updated.values())))
        if all((classes[s] == classes[t]) == (updated[s] == updated[t])
               for s in STATES for t in STATES):
            return updated, sizes
        classes = updated
    raise AssertionError("finite partition refinement did not stabilize")


def lattice():
    coords = (-1, 0, 1)
    segments = ((-1, 0), (0, 1))
    bonds = set()
    for axis in range(3):
        for lo, hi in segments:
            for fixed in product(coords, repeat=2):
                start = list(fixed)
                start.insert(axis, lo)
                end = list(fixed)
                end.insert(axis, hi)
                bonds.add((tuple(start), tuple(end)))
    assert len(bonds) == 54
    assert all(sum(abs(a-b) for a,b in zip(s,t)) == 1
               for s,t in bonds)
    squares = set()
    for i, j in ((0, 1), (0, 2), (1, 2)):
        remaining = ({0, 1, 2} - {i, j}).pop()
        for (a,b), (c,d), fixed in product(segments, segments, coords):
            p = [0, 0, 0]
            p[i], p[j], p[remaining] = a, c, fixed
            q, r = p.copy(), p.copy()
            q[i] = b
            r[j] = d
            end = p.copy()
            end[i], end[j] = b, d
            p, q, r, end = map(tuple, (p,q,r,end))
            assert (p,q) in bonds and (p,r) in bonds
            assert (q,end) in bonds and (r,end) in bonds
            squares.add((i,j,p,end))
    assert len(squares) == 36
    return len(bonds), len(squares)


def main():
    classes, sizes = refine()
    assert len(set(code(s) for s in STATES)) == 18
    assert len(set(diagnostic(s) for s in STATES)) == 18
    assert all((code(s) == code(t))
               == (diagnostic(s) == diagnostic(t))
               == (classes[s] == classes[t])
               for s in STATES for t in STATES)
    assert all(code(step(a, s)) == code(step(a, (s[0], not s[1], *s[2:])))
               for s in STATES for a in ACTIONS)
    bonds, squares = lattice()
    print("PASS: states=64 future-classes=18")
    print("PASS: partition refinement sizes=" + ",".join(map(str, sizes)))
    print("PASS: 5 diagnostic histories exactly recover the minimal quotient")
    print(f"PASS: nonperiodic cube has {bonds} bonds and {squares} squares")


if __name__ == "__main__":
    main()
