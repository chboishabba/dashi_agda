#!/usr/bin/env python3
"""Exact rational finite-measure regression for P0.06 signed moments.

This is an independent model of finite positive sums, not an SU(N)
Haar/Agda kernel receipt, nor an original RG-error estimate.
"""
from fractions import Fraction
from itertools import product


def main() -> None:
    weights = tuple(Fraction(x) for x in (0, 1, 2, 3))
    values = tuple(Fraction(x, 2) for x in (-2, -1, 0, 1, 2))
    tested = 0
    for w in product(weights, repeat=3):
        partition = sum(w)
        if partition == 0:
            continue
        for observable in product(values, repeat=3):
            numerator = sum(a * f for a, f in zip(w, observable))
            assert numerator <= partition
            assert -numerator <= partition
            assert abs(numerator) <= partition
            assert abs(numerator / partition) <= 1
            tested += 1

    assert tested == 7875
    # Unit cancellation and boundedness cannot yield a small RG error:
    # the difference of two Dirac expectations on [-1,1] reaches 2.
    assert abs(Fraction(1) - Fraction(-1)) == 2
    print(
        f"PASS {tested} exact rational signed finite-measure cases; "
        "sharp two-Dirac discrepancy control"
    )


if __name__ == "__main__":
    main()
