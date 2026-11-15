#!/usr/bin/env python3
"""Exact rational sanity checks for the Bałaban T4 semantic P0 cut.

Supplementary regression only: source-written Agda remains the proof authority.
In particular this does not instantiate the physical Wilson/ghost/Haar
integrand, prove a sine-squared lower bound, or certify four quadratures.
"""
from fractions import Fraction
from itertools import product
from math import comb

INNER = ("negativeInner", "positiveInner")
OUTER = ("negativeOuter", "positiveOuter")
CELLS = INNER + OUTER


def actual_quotient_hull(numer, denom):
    assert denom[0] > 0 and denom[0] <= denom[1]
    corners = [x / y for x in numer for y in denom]
    return min(corners), max(corners)


def naive_sign_blind_quotient(numer, denom):
    return numer[0] / denom[1], numer[1] / denom[0]


def main():
    ranks = {i: 0 for i in range(5)}
    for cell in product(CELLS, repeat=4):
        rank = sum(coord in OUTER for coord in cell)
        ranks[rank] += 1
        # Nat-only finite contribution, *not* the analytic q-hat bound.
        assert 2 * rank == sum(2 if coord in OUTER else 0 for coord in cell)

    assert [ranks[i] for i in range(5)] == [16, 64, 96, 64, 16]
    assert all(ranks[i] == 16 * comb(4, i) for i in range(5))
    assert sum(ranks[i] for i in range(1, 5)) == 240

    # This is the genuine endpoint hull for a strictly positive denominator.
    for numerator in (
        (Fraction(-2), Fraction(1)),
        (Fraction(-2), Fraction(-1)),
        (Fraction(1), Fraction(2)),
        (Fraction(0), Fraction(1)),
    ):
        denominator = (Fraction(2), Fraction(4))
        actual = actual_quotient_hull(numerator, denominator)
        proposed = naive_sign_blind_quotient(numerator, denominator)
        assert all(actual[0] <= x/y <= actual[1]
                   for x in numerator for y in denominator)
        if numerator[0] < 0:
            assert proposed != actual, "sign-blind division would be unsound"
        else:
            assert proposed == actual

    actual = actual_quotient_hull(
        (Fraction(-2), Fraction(1)), (Fraction(2), Fraction(4)))
    assert actual == (Fraction(-1), Fraction(1, 2))
    assert naive_sign_blind_quotient(
        (Fraction(-2), Fraction(1)), (Fraction(2), Fraction(4))
    ) == (Fraction(-1, 2), Fraction(1, 2))
    print("PASS 256 generated cells, 16 infrared, orbit sizes 64/96/64/16")
    print("PASS finite two-per-outer-axis rank tally on every generated cell")
    print("PASS sign-aware rational interval quotient counterexample")
    print("OPEN literal Wilson/ghost/Haar symmetry, physical sine bound, quadratures")


if __name__ == "__main__":
    main()
