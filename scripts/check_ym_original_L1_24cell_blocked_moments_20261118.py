#!/usr/bin/env python3
"""Independent exact Fraction regression for the three-class 24-cell blocked RG moments.

Verifies arithmetic only. Does NOT prove the 24^4 conditional-moment
source table, Agda kernel acceptance, exponential Gibbs or continuum RG.
"""
from fractions import Fraction as Q

weights = (Q(78955, 82944), Q(422191, 442368), Q(35459, 36864))
counts = (6, 16, 2)
t_values = (Q(0), Q(1, 4), Q(1))

def raw_moment(power):
    return sum(c * w * t**power
               for c, w, t in zip(counts, weights, t_values)) / 24

z = raw_moment(0)
first = raw_moment(1)
second = raw_moment(2)
mean = first / z
second_normalized = second / z
variance = second_normalized - mean * mean

expected = (
    (z, Q(140731, 147456)),
    (first, Q(634945, 2654208)),
    (second, Q(1273207, 10616832)),
    (mean, Q(634945, 2533158)),
    (second_normalized, Q(1273207, 10132632)),
    (variance, Q(806306942803, 12833778905928)),
)
for actual, target in expected:
    assert actual == target, (actual, target)
assert variance > 0
assert sum(counts) == 24
print("PASS: 6/6 exact blocked partition/moment identities; positive variance")
