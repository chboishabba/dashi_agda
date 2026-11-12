#!/usr/bin/env python3
"""Exact rational tests of X(F)=(Ef-Eb) Zf Zb; not an Agda/Clay receipt."""
from fractions import Fraction
from itertools import product


def check() -> None:
    numerators = tuple(map(Fraction, (-3, -1, 0, 1, 3)))
    positive_partitions = tuple(map(Fraction, (1, 2, 3, 5)))
    trials = 0
    for nf, nb, zf, zb in product(
        numerators, numerators, positive_partitions, positive_partitions
    ):
        ef = nf / zf
        eb = nb / zb
        x = nf * zb - nb * zf
        assert x == (ef - eb) * (zf * zb)
        trials += 1

    for zf, zb in product(positive_partitions, repeat=2):
        assert zf * zb - zb * zf == 0

    # Distinct normalized nonnegative finite two-point Dirac laws.
    # For F = 1_{right}, Nfine=1, Nbare=0, Zfine=Zbare=1.
    assert Fraction(1) * Fraction(1) - Fraction(0) * Fraction(1) == 1
    print(
        f"PASS {trials} exact rational original-form factorization cases; "
        "unit and nonconstant negative controls"
    )


if __name__ == "__main__":
    check()
