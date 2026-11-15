#!/usr/bin/env python3
"""Exact rational finite noncommutative Haar-fiber regression.

D4 is not SU(N), this is neither an Agda kernel check nor a physical
renormalization proof. It exercises native multiplication, inversion,
weighted nonfactorizing two-link density, and normalized Haar sums.
"""
from fractions import Fraction
from random import Random

G = tuple((r, s) for s in (0, 1) for r in range(4))
IDENTITY = (0, 0)


def prod(a, b):
    r, s = a
    q, t = b
    return ((r + (-1 if s else 1) * q) % 4, (s + t) % 2)


def inverse(a):
    return next(b for b in G
                if prod(a, b) == IDENTITY and prod(b, a) == IDENTITY)


def avg(values):
    return sum(values, Fraction(0)) / len(G)


def test_case(density, observable):
    fine = avg(
        avg(density[u, v] * observable[prod(u, v)] for v in G)
        for u in G
    )
    rho = {
        w: avg(density[u, prod(inverse(u), w)] for u in G)
        for w in G
    }
    coarse = avg(rho[w] * observable[w] for w in G)
    assert fine == coarse, (fine, coarse)
    z_fine = avg(avg(density[u, v] for v in G) for u in G)
    z_coarse = avg(rho.values())
    assert z_fine == z_coarse
    return fine


def main():
    rng = Random(1444)
    for u in G:
        assert prod(inverse(u), u) == IDENTITY
        for v in G:
            assert prod(inverse(u), prod(u, v)) == v
    for _ in range(512):
        density = {
            (u, v): Fraction(rng.randrange(10), rng.randrange(1, 7))
            for u in G for v in G
        }
        observable = {
            w: Fraction(rng.randrange(-8, 9), rng.randrange(1, 7))
            for w in G
        }
        test_case(density, observable)
    one = {w: Fraction(1) for w in G}
    uniform = {(u, v): Fraction(1) for u in G for v in G}
    assert test_case(uniform, one) == 1
    indicator = {w: Fraction(int(w == (1, 1))) for w in G}
    assert test_case(uniform, indicator) == Fraction(1, len(G))
    print("PASS 512 exact rational D4 noncommutative Haar fiber identities")


if __name__ == "__main__":
    main()
