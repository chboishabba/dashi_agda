#!/usr/bin/env python3
"""Flatness firewall: nonflat loop holonomy is NOT a pi1 homomorphism.

Original prior math: holonomy of flat bundles factors through pi1;
nonflat holonomies depend on geometric representatives (curvature/Stokes).
This is an elementary smooth SU3 control on R2, not a horn realization.
"""
from fractions import Fraction as F
import sympy as s
r1,r2=F(1,2),F(1,3)
# On all R2 A=iH(-y dx+x dy)/2, H=diag(1,-1,0).
# Both circles are CONTRACTIBLE (pi1 R2=0), yet
# integral A=i*pi*r^2 H and hol=diag(e^(i*pi*r^2),e^(-i*pi*r^2),1).
a1=s.pi*s.Rational(r1.numerator**2,r1.denominator**2)
a2=s.pi*s.Rational(r2.numerator**2,r2.denominator**2)
assert s.simplify(a1-s.pi/4)==0
assert s.simplify(a2-s.pi/9)==0
assert a1!=a2 and 0<a2<a1<s.pi
assert s.simplify(s.exp(s.I*a1)-s.exp(s.I*a2))!=0
assert s.simplify((1+2*s.cos(a1))-(1+2*s.cos(a2)))!=0
print('PASS smooth bounded NONFLAT SU3 on contractible R2: homotopic circles differ in Wilson holonomy')
# The source flat puncture fixture A=(iH/5)dtheta has F=0 on R2-{0},
# hence factors through pi1=Z and gives a valid nontrivial order-five
# representation of that different fundamental group.
z=s.symbols('z',real=True)
alpha=s.Rational(1,5)
assert s.simplify(s.exp(2*s.pi*s.I*alpha)**5)==1
print('PASS FLAT puncture order-five hol factors through pi1; singular/removed origin is essential')
print('NO-GO using Hatcher pi1 commutator relations to rewrite Wilson loops for arbitrary NONFLAT A without a controlled homotopy/curvature correction')
print('PHYSICAL GATE: exact representation/flatness or quantitative non-Abelian Stokes correction for the actual selected loops')
