#!/usr/bin/env python3
"""Exact *formal* endpoint-local anomaly cochain, not quantum gauge invariance.

Original anomaly-inflow framework: Scrucca et al. (2002), von Gersdorff &
Quiros (2003). Source-selected 27 charges, Chi33, and CS/WZ construction:
chboishabba/dashi_agda PR #1241; E6 trinification source PR #1106.
This regression tests linear endpoint gauge parameters, formal polynomial
coefficients, and the rank of their cancellation equations. It does NOT
claim an integral characteristic class, a valid large-gauge transformation,
or an APS/eta-regularized fermion determinant.
"""
import sympy as S

fl, fr, p1, c, l, r = S.symbols("FL FR p1 c2c c2L c2R")
a0, a1, k, w = S.symbols("alpha0 alpha1 k w")
X4 = 40*fl**2 + 64*fl*fr + 40*fr**2 + 16*p1 + 2*(c+l+r)
I6 = S.expand((fl-fr)*X4)
assert S.expand(I6.subs({fl:fr})) == 0
# Normalise the gauge parameter alpha along FL-FR, not along photon.
# Fermionic half-anomaly at both fixed points, opposite bulk inflow,
# one source phase supported ONLY at endpoint zero.
A0 = S.Rational(1,2) + k - 2*w
A1 = S.Rational(1,2) - k
solution = S.solve((A0,A1),(k,w), dict=True)
assert solution == [{k:S.Rational(1,2),w:S.Rational(1,2)}]
residual = S.expand((a0*A0+a1*A1)*X4).subs(solution[0])
assert residual == 0
assert S.solve((A0.subs(w,0), A1.subs(w,0)),k) == []
assert S.expand((a0*S.Rational(1,2)+a1*S.Rational(1,2))*X4) != 0
# Second endpoint-local counterterm is not needed, but is a different
# source ansatz; do not infer uniqueness of all possible anomaly repairs.
assert S.expand(X4/2).coeff(c) == 1
assert S.expand(X4/4).coeff(c) == S.Rational(1,2)
print("PASS unique (k,w) for this specified one-end linear ansatz:",solution[0])
print("PASS independent formal endpoint parameters and polynomial identity")
print("PASS CS-only fails; symmetric two-end half-unit distinct from one-end")
print("OPEN true (SU3^3)/Z3 characteristic-class lattice and spin global phase")
print("OPEN 5D descent/eta, boundary-local Chi phase, and full quantum action")
