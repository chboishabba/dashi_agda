#!/usr/bin/env python3
"""R823 local-continuity cut: exact original R850/R854 scalar controls.

An independently evaluated real continuous rate with r(0)<0 has a negative
integral on a short interval. This elementary analytic theorem does NOT itself
identify the R408/R823 rational packet with a real Galerkin trajectory.
No endpoint closure is asserted by this regression.
"""
from fractions import Fraction as Q

C, P, D = Q(-557627, 125), Q(0), Q(15834)
r0 = 6 * (12 * C - P + D)
assert r0 == Q(-28273644, 125) and r0 < 0

# Original R828/R854 physical-Fourier enclosure constants, not an
# assertion that Agda's rational R408 trajectory has been constructed.
K = 5032512
L = 391309593930357307785216
T = Q(226189, 3938540454339300631433585885184)
assert K > 0 and L > 0 and T > 0
assert K * T < 6  # M=12 with initial component maximum <=6
assert L * K * T == Q(226189, 2)
rate_at_most = r0 + L * K * T
assert rate_at_most == -Q(28273663, 250)
assert rate_at_most < -Q(226189, 2) < 0
integral_at_most = r0 * T + Q(L*K, 2) * T*T
assert integral_at_most < 0

# Separate classical epsilon-delta lemma:
# If r:[0,a)->R is continuous at 0 and r(0)=r0<0, choose
# epsilon=-r0/2>0. Some eta>0 obeys
# |r(t)-r0|<epsilon on [0,eta], so
# integral_0^h r(t)dt < (r0/2)*h < 0 for all 0<h<=eta.
# The continuity hypothesis is essential: a step rate with
# r(0)=r0<0 and r(t)=1 for t>0 defeats the implication.
print("R850 initial signed rate:", r0)
print("R854 rate upper:", rate_at_most)
print("R854 integrated affine upper:", integral_at_most)
print("PASS: exact scalar checks; original R408 real same-source weld OPEN")
