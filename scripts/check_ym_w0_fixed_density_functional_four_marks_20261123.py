#!/usr/bin/env python3
"""W0 exact geometry regression: one fixed positive fibre law, four observables.

Illustrative finite conditional law (not actual continuous SU(N) Haar,
Eq.(1.71) localization, source-selected omega/lambda/S geometry or Clay).
"""
from fractions import Fraction
from itertools import product

fields = ((0, 0), (0, 2), (2, 0), (2, 2))
wilson_weights = tuple(map(Fraction, (2, 1, 3, 4)))

# One single operator. The Wilson weight and domain are NOT redefined by marks.
def fixed_T(observable):
    return sum(w * observable(f, g)
               for w, (f, g) in zip(wilson_weights, fields))

K0 = fixed_T(lambda f, g: Fraction(1))
KF = fixed_T(lambda f, g: Fraction(f))
KG = fixed_T(lambda f, g: Fraction(g))
KFG = fixed_T(lambda f, g: Fraction(f * g))
assert (K0, KF, KG, KFG) == (10, 14, 10, 16)
assert K0 * KFG - KF * KG == 20
assert KFG != KF * KG / K0

for s, t in product((Fraction(-1, 10), Fraction(0), Fraction(1, 10)),
                    repeat=2):
    marked = fixed_T(lambda f, g: (1 + s * f) * (1 + t * g))
    polynomial = K0 + s * KF + t * KG + s * t * KFG
    assert marked == polynomial

# Original four-column necessary positivity cone:
assert 0 <= KF <= 2 * K0
assert 0 <= KG <= 2 * K0
assert max(0, 2*KF + 2*KG - 4*K0) <= KFG <= min(2*KF, 2*KG)

# A shortcut that multiplies separate normalized T masses loses c.
assert K0 + KF / 10 + KG / 10 + KFG / 100 != (
    (K0 + KF / 10) * (K0 + KG / 10) / K0
)

print("PASS 9/9 exact two-source evaluations against fixed unmarked T")
print("PASS K0=10 KF=14 KG=10 KFG=16")
print("PASS covariance numerator 20 retained; factorized shortcut rejected")
print("PASS four-column positive cone")
print("NO original SU(N) Haar, literal CMP119 step or all-cutoff claim")
