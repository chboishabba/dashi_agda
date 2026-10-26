#!/usr/bin/env python3
"""Exact finite NV photon binary-discrimination experiment (no device claims).

Source owner: MCG #1238 photon likelihood; analytical companion to stacked
Agda #1269. Rational equal-prior Bayes risk for conditionally iid histories.
"""
from fractions import Fraction
from itertools import product

def distribution(p, n):
    assert Fraction(0) <= p <= Fraction(1)
    q = 1 - p
    return {bits: p ** sum(bits) * q ** (n - sum(bits))
            for bits in product((0, 1), repeat=n)}

def risk(p, q, n):
    a, b = distribution(p, n), distribution(q, n)
    assert sum(a.values()) == sum(b.values()) == 1
    # Bayes error under equal priors: half sum of overlapping masses.
    return sum(min(a[x], b[x]) for x in a) / 2

def check():
    grid = [Fraction(k, 5) for k in range(6)]
    for n in range(8):
        for p in grid:
            for q in grid:
                e = risk(p, q, n)
                assert Fraction(0) <= e <= Fraction(1, 2)
                assert e == risk(q, p, n)
                if p == q:
                    assert e == Fraction(1, 2)
                if n == 0:
                    assert e == Fraction(1, 2)
                if n < 7:
                    assert risk(p, q, n + 1) <= e
    assert risk(Fraction(4, 5), Fraction(1, 5), 1) == Fraction(1, 5)
    assert risk(Fraction(4, 5), Fraction(1, 5), 2) == Fraction(1, 5)
    assert risk(Fraction(4, 5), Fraction(1, 5), 3) == Fraction(13, 125)
    print("PASS: exact iid finite-history normalization, symmetric optimal Bayes risk, "
          "equal-kernel collision and non-increasing error (n=0..7, 36 pairs).")

if __name__ == "__main__":
    check()
