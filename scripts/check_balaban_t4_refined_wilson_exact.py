#!/usr/bin/env python3
"""Exact Q reference only: original 256-cell Wilson denominator via refined square.

This confirms *arithmetic*, not Agda kernel or physical Fourier membership.
The four rank enclosures below are for an AUXILIARY FREE WILSON PROPAGATOR,
not Bałaban's Wilson+ghost+Haar vacuum-polarization beta integrand.
"""
from fractions import Fraction as Q
from itertools import product
from collections import Counter

floor = Q(7569, 4096)
sine_lo = Q(87, 128)
CELLS = {
    "negativeOuter": (-Q(1), -sine_lo),
    "negativeInner": (-Q(1), Q(1)),
    "positiveInner": (-Q(1), Q(1)),
    "positiveOuter": (sine_lo, Q(1)),
}

def mul_interval(a, b):
    corners = [x*y for x in a for y in b]
    return min(corners), max(corners)

def square_interval(a):
    lo, hi = mul_interval(a, a)
    return max(Q(0), lo), hi

def component(c):
    return mul_interval((Q(4), Q(4)), square_interval(CELLS[c]))

def sum_interval(a, b):
    return a[0] + b[0], a[1] + b[1]

def denom(cell):
    out = (Q(0), Q(0))
    for c in cell:
        out = sum_interval(out, component(c))
    return out

def flipped(c):
    return {
        "negativeOuter": "positiveOuter", "positiveOuter": "negativeOuter",
        "negativeInner": "positiveInner", "positiveInner": "negativeInner"
    }[c]

def seven_actions(cell):
    for i in range(4):
        other = list(cell)
        other[i] = flipped(other[i])
        yield tuple(other)
    for i in range(3):
        other = list(cell)
        other[i], other[i+1] = other[i+1], other[i]
        yield tuple(other)

def main():
    count = Counter()
    cells = list(product(CELLS, repeat=4))
    assert len(cells) == 256
    for cell in cells:
        rank = sum('Outer' in c for c in cell)
        count[rank] += 1
        lo, hi = denom(cell)
        assert (lo, hi) == (rank * floor, Q(16)), (cell, lo, hi)
        if rank:
            assert lo >= floor > 0
        else:
            assert lo == 0
        for g in seven_actions(cell):
            assert denom(g) == (lo, hi), (cell, g)
    assert [count[i] for i in range(5)] == [16, 64, 96, 64, 16]
    print("PASS 256 exact source boxes, 16 IR, 240 regular; 1792 seven-generator endpoint equalities")
    print("PASS physical-bound TARGET strict rational lower 7569/4096 on all regular unshifted Wilson denominators")

    weights = (4, 6, 4, 1)
    low, high = Q(0), Q(0)
    for rank, weight in enumerate(weights, 1):
        lower = Q(1,16)
        upper = Q(4096, rank*7569)
        low += weight*lower
        high += weight*upper
        print(f"rank {rank}: auxiliary free Wilson 1/hat(k)^2 enclosure [{lower}, {upper}], weight {weight}")
    assert (low, high) == (Q(15, 16), Q(105472, 22707))
    print(f"PASS auxiliary direct-interval bound, all regular boxes: [{low}, {high}]")
    print("NOT the requested original Wilson/ghost/Haar four beta integrals")
    print("OPEN: physical Fourier/Machin sine membership, shifted denominators, source tensor scalar, quadrature integrand+error proofs")

if __name__ == "__main__":
    main()
