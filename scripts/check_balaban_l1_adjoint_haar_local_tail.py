#!/usr/bin/env python3
"""Independent exact rational checks for the adjoint Haar local-tail budget.

Does NOT prove the analytic Euler product or identify the original physical
Bałaban gauge-fixed finite-cutoff Wilson/FP/Haar source.
"""
from fractions import Fraction
from math import log, sin

q = Fraction
quartic = q(1, 1440)
zeta_tail_bound = q(6, 5)
ratio = q(1, 36)

first_shell_coefficient = q(2) * zeta_tail_bound / 3
assert first_shell_coefficient == q(4, 5)
tail_bound = first_shell_coefficient * ratio**3 / (1 - ratio)
assert tail_bound == q(1, 56700)
fourth_and_higher = quartic + tail_bound
assert fourth_and_higher == q(323, 453600)
adjoint_casimir = fourth_and_higher / 2
assert adjoint_casimir == q(323, 907200)

checks = 0
for r in (0.25, 0.4, 0.7, 0.9, 1.0):
    effective_haar_action = -2 * log(sin(r/2)/(r/2))
    rem6 = effective_haar_action - r*r/12 - r**4/1440
    assert -1e-13 <= rem6 <= r**6/56700 + 1e-13
    checks += 1
print(f"PASS: exact rational tail budget and Casimir factor, {checks} SU(2) diagnostics")
