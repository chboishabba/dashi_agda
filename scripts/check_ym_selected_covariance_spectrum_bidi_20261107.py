#!/usr/bin/env python3
"""Exact rational negative control: selected decay is not the full OS gap.

A 3D positive symmetric transfer operator has normalized vacuum 1,
a selected local fast direction 1/2, and an unobserved slow direction
n/(n+1). The selected covariance is 2^-t for every n, while the
full transfer spectral gap is 1/(n+1) -> 0. No numerical tolerance.
This is an exact finite-dimensional falsifier, NOT a physical YM model.
"""
from fractions import Fraction

for n in (3, 7, 31, 127):
    vacuum = Fraction(1)
    fast = Fraction(1, 2)
    slow = Fraction(n, n + 1)
    for time in range(1, 9):
        selected_covariance = fast ** time
        undetected_slow_covariance = slow ** time
        assert selected_covariance <= Fraction(1, 2) ** time
        assert undetected_slow_covariance > selected_covariance
    assert slow < vacuum
    print(
        f"n={n} selected_decay_ratio={fast} "
        f"undetected_ratio={slow} full_transfer_gap={vacuum-slow}"
    )
print("PASS: one selected covariance decay cannot certify the whole spectrum")
