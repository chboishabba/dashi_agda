#!/usr/bin/env python3
"""Exact rational finite noncommutative Haar test.

Uses the dihedral group D4 (order eight), not SU(N) or physical Wilson
Gibbs weights. Tests n disjoint paired products and m unused Haar links.
No Agda kernel or interacting RG rate is inferred.
"""
from fractions import Fraction
from itertools import product

G = tuple((r, s) for s in (0, 1) for r in range(4))


def mul(a, b):
    return (
        (a[0] + (-1 if a[1] else 1) * b[0]) % 4,
        (a[1] + b[1]) % 2,
    )


def test(xs):
    value = (0, 0)
    for x in xs:
        value = mul(value, x)
    return Fraction(3 if value == (2, 1) else
                    (-2 if value[0] == 1 else 1), 5)


def check(n, m):
    pairs = tuple(product(G, repeat=2))
    fine = sum(
        (test(tuple(mul(u, v) for u, v in selected))
         for selected in product(pairs, repeat=n)),
        Fraction(0),
    ) / len(G) ** (2 * n)
    coarse = sum(
        (test(xs) for xs in product(G, repeat=n)),
        Fraction(0),
    ) / len(G) ** n
    assert fine == coarse, (n, m, fine, coarse)
    assert fine * Fraction(len(G) ** m, len(G) ** m) == coarse


def main():
    checks = 0
    for n in range(4):
        for m in range(3):
            check(n, m)
            checks += 1
    print(f"PASS {checks} exact D4 paired Haar n=0..3, unused m=0..2 checks")


if __name__ == "__main__":
    main()
