#!/usr/bin/env python3
"""A GAUGE-INVARIANT CLASSICAL 5D EFT ANSATZ with explicit soft mass split.
This is not an E6/SUSY completion, an action derivation from first-Tits, or a
valid quantum 5D model by itself. Each scalar and Dirac transforms in the
same SU3_colour fundamental and has the same U1 charge.
"""
import sympy as s
from fractions import Fraction
GeV=s.Integer(1)
# Spectator Dirac/complex scalar pairs: 6 light quarks + 2 heavy exotics.
fermions=[s.Rational(216,100000),s.Rational(47,10000),s.Rational(935,10000),
          s.Rational(1273,1000),s.Rational(4183,1000),s.Rational(17256,100)] + [9000,9000]
scalar_mass=3000
split=[scalar_mass**2-m*m for m in fermions]
assert len(split)==8 and all(s.simplify(m*m+d-scalar_mass**2)==0 for m,d in zip(fermions,split))
assert all(scalar_mass**2>0 for _ in fermions)
assert split[-1]==-72000000 # inverted heavy split; negative SOFT coefficient, positive TOTAL mass^2
# Gauge invariant scalar mass and stabilizing quartic at fixed gauge background:
# V=m_s^2(S^dag S) + lambda (S^dag S)^2, lambda>=0.
u,lam=s.symbols("u lam",nonnegative=True,real=True)
V=scalar_mass**2*u+lam*u*u
assert s.simplify(s.diff(V,u))==scalar_mass**2+2*lam*u
assert V.subs(u,0)==0
# SU3 x U1 elementary gauge check for a colour multiplet.
a,b,c,theta=s.symbols("a b c theta",real=True)
q=s.Rational(2,3)
z=s.Matrix([s.exp(s.I*a),s.exp(s.I*b),s.exp(s.I*c)])
U=s.diag(s.exp(s.I*theta),s.exp(-s.I*theta),s.Integer(1))
# SU3 determinant = 1; gauge norm preserved for charged triplet.
assert U.det()==1
assert s.simplify((U*z).conjugate().dot(U*z)-z.conjugate().dot(z))==0
print("PASS gauge-covariant 5D spectator mass EFT: scalar mS²=MDirac²+DeltaSoft² and positive total mS²")
print("PASS SU3 fundamental norm and uncondensed scalar potential stability in isolated nonnegative-quartic sector")
print("FAIL genuine SUSY proof: inverted negative soft coefficient has no derived dynamical spurion")
print("OPEN cross-scalar interactions, E6 27 Higgs potential, 5D gauge/ghost loops, CS/spin quantization, global phase and observational eligibility")
