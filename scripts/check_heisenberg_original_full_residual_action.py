#!/usr/bin/env python3
"""Deterministic executable finite-model regression for the original H_6 law.

Matches the source operations:
  (x,xi,c)*(y,eta,d) = (x+y,xi+eta,c+d+xi.y), arithmetic F3.
The full relation-coordinate action left-multiplies the original 13-word
and carries all 131 omitted ordered relation cells without change.

This regression does NOT typecheck the Agda source or admit a physical/
appraisal/ITIR action. It checks independent finite algebra.
"""
from random import Random

N = 6
ZERO = (0,) * N
IDENTITY = (ZERO, ZERO, 0)

def add(a, b):
    return tuple((x + y) % 3 for x, y in zip(a, b))

def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % 3

def compose(g, h):
    x, xi, c = g
    y, eta, d = h
    return add(x, y), add(xi, eta), (c + d + dot(xi, y)) % 3

def inverse(g):
    x, xi, c = g
    return (
        tuple((-v) % 3 for v in x),
        tuple((-v) % 3 for v in xi),
        (-c + dot(xi, x)) % 3,
    )

def act(g, state):
    word, residual = state
    return compose(g, word), residual

def check():
    rng = Random(369)
    for _ in range(20_000):
        def group_element():
            return (
                tuple(rng.randrange(3) for _ in range(N)),
                tuple(rng.randrange(3) for _ in range(N)),
                rng.randrange(3),
            )
        g, h, k = group_element(), group_element(), group_element()
        residual = tuple(rng.randrange(3) for _ in range(131))
        state = group_element(), residual
        assert compose(compose(g, h), k) == compose(g, compose(h, k))
        assert compose(IDENTITY, g) == g == compose(g, IDENTITY)
        assert compose(inverse(g), g) == IDENTITY
        assert compose(g, inverse(g)) == IDENTITY
        assert act(compose(g, h), state) == act(g, act(h, state))
        assert act(IDENTITY, state) == state
        assert act(inverse(g), act(g, state)) == state
        assert act(g, state)[1] == residual

    translation = ((1, 0, 0, 0, 0, 0), ZERO, 0)
    modulation = (ZERO, (1, 0, 0, 0, 0, 0), 0)
    assert compose(translation, modulation) != compose(modulation, translation)
    print("PASS: 20000 seeded original-cocycle and 13+131 action trials")
    print("PASS: inverse, unit, associativity, residual invariance, noncommutativity")

if __name__ == "__main__":
    check()
