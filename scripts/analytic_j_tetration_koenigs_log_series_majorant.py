#!/usr/bin/env python3
"""Exact Fraction tests of Koenigs logarithmic-series majorants.

This checks rational implications only. It does NOT construct the Bishop
principal-log series, selected fixed point, or global Kneser normalization.
"""
from fractions import Fraction as F

A = F(137, 100)
R = F(1, 10)
P_UPPER = F(69, 50)
Q = F(4, 5)
M = F(1, 2) / (A * (A - R))
BETA = P_UPPER * Q * Q
PREF = P_UPPER * M / (1 - BETA)

def tail(n: int, radius: F) -> F:
    if n < 0 or not F(0) <= radius <= R:
        raise ValueError("require n >= 0 and 0 <= radius <= 1/10")
    return PREF * BETA**n * radius**2

def check() -> None:
    assert A - R == F(127, 100)
    assert 1 / (A - R) == F(100, 127) < Q
    assert M == F(5000, 17399) < F(311, 1000)
    assert BETA == F(552, 625) < 1
    assert PREF == F(4312500, 1270127)
    assert PREF < F(21459, 5840)
    assert P_UPPER * M * sum(BETA**k for k in range(25)) == PREF * (1 - BETA**25)
    for radius in [F(1, 10), F(1, 1000)]:
        for n in [0, 1, 10, 40, 80, 200]:
            assert tail(n + 1, radius) == BETA * tail(n, radius)
            assert tail(n, radius) >= 0
    print("PASS q = 100/127 < 4/5, M =", M)
    print("PASS beta =", BETA, "Koenigs prefactor =", PREF)
    print("PASS exact Fraction majorants, not Bishop analytic acceptance")

if __name__ == "__main__":
    check()
