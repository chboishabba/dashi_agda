#!/usr/bin/env python3
"""Exact P3^3 hypervoxel standing waves and finite quantum walk at t=pi.

Finite Z/Q mathematics; no inference of continuum QM, Einstein dynamics,
physical string theory or Clay. Existing 369 hypervoxel path adjacency.
"""
from fractions import Fraction as Q
from itertools import product

SITES = tuple(product((-1, 0, 1), repeat=3))
MODES = tuple(product(range(3), repeat=3))
BASIS1 = ((1, 1, 1), (1, 0, -1), (1, -2, 1))
LAM1 = (0, 1, 3)
NORMS1 = (3, 2, 6)


def phi(k, x):
    return BASIS1[k[0]][x[0]+1] * BASIS1[k[1]][x[1]+1] * BASIS1[k[2]][x[2]+1]


def eigenvalue(k):
    return LAM1[k[0]] + LAM1[k[1]] + LAM1[k[2]]


def mode_norm(k):
    return NORMS1[k[0]] * NORMS1[k[1]] * NORMS1[k[2]]


def laplace(f, x):
    total = 0
    for axis in range(3):
        for step in (-1, 1):
            y = list(x)
            y[axis] += step
            if -1 <= y[axis] <= 1:
                total += f(x) - f(tuple(y))
    return total


def forward(state):
    return {k: Q(sum(state[x]*phi(k, x) for x in SITES), mode_norm(k))
            for k in MODES}


def inverse(coeff):
    return {x: sum((coeff[k]*phi(k, x) for k in MODES), Q(0))
            for x in SITES}


def u1(x, y):
    # Spectrum of L(P3): 0,1,3; at pi the phases are +1,-1,-1.
    return Q(2, 3) - (1 if x == y else 0)


def u(x, y):
    # L(P3^3) is the Kronecker sum, so U is Kronecker product.
    return u1(x[0], y[0]) * u1(x[1], y[1]) * u1(x[2], y[2])


def evolve(state):
    return {x: sum((u(x, y)*state[y] for y in SITES), Q(0))
            for x in SITES}


def norm(state):
    return sum((state[x]**2 for x in SITES), Q(0))


def run():
    assert len(SITES) == 27 and len(MODES) == 27
    for k in MODES:
        for x in SITES:
            assert laplace(lambda y: phi(k, y), x) == eigenvalue(k)*phi(k, x)
    for a in MODES:
        for b in MODES:
            assert sum(phi(a, x)*phi(b, x) for x in SITES) == (
                mode_norm(a) if a == b else 0)
    for x in SITES:
        for y in SITES:
            assert sum((Q(phi(k, x)*phi(k, y), mode_norm(k)) for k in MODES),
                       Q(0)) == (1 if x == y else 0)
    state = {x: Q(2*x[0]-x[1]) for x in SITES}
    assert inverse(forward(state)) == state
    for x in SITES:
        for y in SITES:
            assert u(x, y) == u(y, x)
            assert sum((u(x, z)*u(z, y) for z in SITES), Q(0)) == (
                1 if x == y else 0)
    moved = evolve(state)
    assert norm(state) == norm(moved) and evolve(moved) == state
    centre = (0, 0, 0)
    localized = {x: Q(1) if x == centre else Q(0) for x in SITES}
    born = evolve(localized)
    assert sum((v*v for v in born.values()), Q(0)) == 1
    assert born[centre] == Q(-1, 27)
    assert born[(-1, -1, -1)] == Q(8, 27)
    assert born[centre]**2 == Q(1, 729)
    assert born[(-1, -1, -1)]**2 == Q(64, 729)
    print("PASS P3^3 path 27-site eigenbasis/spectrum/orthogonality/completeness")
    print("PASS exact original-graph spectral transform and inverse")
    print("PASS 27x27 U(pi) rational orthogonal involution")
    print("PASS norm and Born probabilities (centre=1/729; corner=64/729)")
    print("BOUNDARY finite toy quantum walk only, no QFT/GR/string/Clay")


if __name__ == "__main__":
    run()
