#!/usr/bin/env python3
"""Exact rational regressions for the selected Bałaban Typed interval arithmetic.

No floats, no CI dependency. Tests the physical-source four-corner
min/max definition and the endpoint observational laws. Numerical
regression is NOT Agda kernel acceptance, proof of selected backend
record equality, or the Wilson/ghost/Haar source integrand.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product

def add(x, y):
    return x[0] + y[0], x[1] + y[1]

def mul(x, y):
    corners = [a * b for a, b in product(x, y)]
    return min(corners), max(corners)

def run():
    endpoints = [Q(i, 2) for i in range(-6, 7)]
    intervals = list(combinations_with_replacement(endpoints, 2))
    assert len(intervals) == 91
    for a in intervals:
        for b in intervals:
            assert add(a, b) == add(b, a)
            assert mul(a, b) == mul(b, a)
            assert mul(a, b)[0] <= mul(a, b)[1]
    for a, b, c in product(intervals, repeat=3):
        assert add(add(a,b), c) == add(a, add(b,c))
        assert mul(mul(a,b),c) == mul(a,mul(b,c))
        assert add(a,add(b,c)) == add(b,add(a,c))
    print("PASS: 91 rational intervals / 8,281 commutativity pairs / 753,571 associativity triples")
    print("PASS: exact four-corner arithmetic, additive swaps, all sign configurations")
    print("STATUS: arithmetic regression only; Agda typecheck and physical gates remain open")

if __name__=="__main__":
    run()
