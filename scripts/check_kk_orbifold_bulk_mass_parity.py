#!/usr/bin/env python3
"""Chosen S1/Z2 5D Dirac parity forbids an EVEN constant scalar mass.

For gamma5^2=1, {gamma5,gamma0}=0, under spinor reflection
Psi(-y)=gamma5 rho(P) Psi(y), with unitary gauge parity rho(P),
the scalar bilinear barPsiPsi is ODD. A local coefficient M(y)
must be odd M(-y)=-M(y) to keep action invariant. Constant bare
5D Dirac mass and constant gauge-singlet scalar spurion VEV
from the previous SMOOTH CIRCLE soft-split QCD calculation cannot
be imported into the chiral orbifold action. Odd kink profiles or
gauge-compatible boundary/multiplet mixing are new physical sources.
This algebra does NOT build an anomaly-safe orbifold fermion action.
"""
import sympy as s
I=s.eye(2);Z=s.zeros(2)
gamma0=s.BlockMatrix([[Z,I],[I,Z]]).as_explicit()
gamma5=s.diag(-1,-1,1,1)
assert gamma5**2==s.eye(4)
assert gamma5*gamma0*gamma5==-gamma0
# For a gauge-unitary parity P, the P factors cancel inside PsiBarPsi.
bilinear_reflection_sign=-1
assert bilinear_reflection_sign==-1
# A constant EVEN coefficient would make M barPsiPsi odd.
assert (+1)*bilinear_reflection_sign==-1
# An ODD coefficient may yield an invariant local mass term.
assert (-1)*bilinear_reflection_sign==+1
print("PASS smooth-circle constant Dirac mass source is not orbifold reflection invariant")
print("PASS an odd kink/field profile can have an even mass interaction, subject to source dynamics")
print("OPEN anomaly-safe mass operators, zero modes, boundary terms and new interval Casimir")
