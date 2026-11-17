#!/usr/bin/env python3
"""Independent exact-integer test of the general finite-pair-sieve lift.

Source genealogy:
  Eratosthenes/Brun finite sieve, Selberg parity limitation,
  DHJ Polymath (2014), 10.1186/s40687-014-0012-7.
  Original DASHI certified finite-sieve / period owners are reused.
This verifies identities at finitely many inputs, NOT the Agda kernel,
an unconditional universal CRT theorem, or twin-prime infinitude.
"""
from math import prod, isqrt


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def survives(n, factors):
    return all(n % p != 0 and (n + 2) % p != 0 for p in factors)


def witness(r, P, t):
    left_factor = 1 + P * (r + 2) * t
    right_factor = 1 + P * r * t
    lower = r * left_factor
    upper = (r + 2) * right_factor
    shift = r * (r + 2) * t
    assert lower + 2 == upper
    assert lower == r + shift * P
    return lower, upper, left_factor, right_factor


def check():
    bases = (
        (), (2,), (2, 3), (2, 3, 5), (2, 3, 5, 7, 11),
        (2, 3, 5, 7, 11, 13), (3, 5, 7),
        (2, 2, 3, 3, 5), (5, 7, 11, 13, 17),
    )
    lifts = 0
    for factors in bases:
        assert all(prime(p) for p in factors)
        P = prod(factors)
        assert P >= 1
        # The elementary -1/+1 residue baseline uses no CRT inverse.
        # For the empty list r=2 is a valid vacuous survivor.
        r = 2 * P - 1 if P >= 2 else 2
        assert r >= 2 and survives(r, factors)
        for initial in [r] + [
            k for k in range(2, 100) if survives(k, factors)
        ][:20]:
            for t in (1, 2, 3, 17):
                lower, upper, lf, rf = witness(initial, P, t)
                assert lf > 1 and rf > 1 and initial > 1
                assert lower % initial == 0
                assert upper % (initial + 2) == 0
                assert lower > initial
                assert survives(lower, factors) == survives(initial, factors)
                assert (not prime(lower)) and (not prime(upper))
                assert lower % P == initial % P
                lifts += 1
    print("PASS: exact identities / strict composite certificates / all period residues")
    print("bases:", len(bases), "| certified factorable survivor lifts:", lifts)
    print("includes prime 2, empty axes, repeated axes and prime lists beyond SSP15")
    print("Source-written Agda not kernel-verified; no analytic twin-prime claim")


if __name__ == "__main__":
    check()
