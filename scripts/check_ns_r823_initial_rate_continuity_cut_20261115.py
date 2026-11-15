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
# Source R828 728-mode finite Fourier component estimates, recomputed
# from the original projection/helicity row bounds rather than trusted
# as unexplained hard-coded constants. These are physical real-Fourier
# estimates, not an inhabitant of rational-valued R408 trajectories.
n = (2 * 4 + 1) ** 3 - 1
M, initial_max = 12, 6
projection_row, helicity_row, cross, dot, lap = 4, 3, 2, 12, 48
assert n == 728
force_bound = projection_row * n * dot * M * M
force_state_lipschitz = projection_row * n * 2 * dot * M
ode_bound = force_bound + lap * M
hu, hu_lip = helicity_row * M, helicity_row
hf, hf_lip = helicity_row * force_bound, helicity_row * force_state_lipschitz
mixed = n * cross * hu * hu
mixed_lip = n * cross * 2 * hu * hu_lip
comm = n * 2 * cross * hf * hu
comm_lip = n * 2 * cross * (hf_lip * hu + hf * hu_lip)
work_lip = 2 * n * 3 * (mixed_lip * comm + mixed * comm_lip)
production_lip = 8 * 2 * n * 3 * (force_bound + M * force_state_lipschitz)
dissipation_lip = 8 * n * 3 * lap * 2 * M
rate_state_lipschitz = 6 * (12 * work_lip + production_lip + dissipation_lip)

K = 5032512
L = 391309593930357307785216
assert (ode_bound, rate_state_lipschitz) == (K, L)
assert 0 < initial_max < M

T = Q(226189, 3938540454339300631433585885184)
assert K > 0 and L > 0 and T > 0
assert K * T < M - initial_max
# For the genuine real Galerkin polynomial u'=F(u), the standard
# finite-dimensional continuation/first-exit argument proves
# max |u_k,j(t)| <= initial_max + K*t < M on [0,T].
# Thus |r(u(t))-r(u(0))| <= L*K*t, not merely L*t.
assert K < 10065030  # exact R856 pointwise safe integer multiplier
assert K < 20130061  # exact R856 integrated safe integer multiplier
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
