#!/usr/bin/env python3
"""Exact finite path interference, detector distinguishability and TSFV gate.
No claim of Feynman continuum measure, path completeness or S/hbar source.
"""
import sympy as s
I=s.I
a1=s.Integer(1)
a2=-s.Integer(1)
coh=s.expand((a1+a2)*s.conjugate(a1+a2))
incoh=s.expand(a1*s.conjugate(a1)+a2*s.conjugate(a2))
assert coh==0 and incoh==2
# Variable relative phase; detector responds to complex amplitude sum.
theta=s.symbols("theta",real=True)
a2theta=s.exp(I*theta)
intensity=s.simplify(s.expand_complex((a1+a2theta)*s.conjugate(a1+a2theta)))
assert s.simplify(intensity-(2+2*s.cos(theta)))==0
assert s.simplify(intensity.subs(theta,s.pi)-0)==0
assert s.simplify(intensity.subs(theta,0)-4)==0
# Adding fully distinguishable path markers removes off-diagonal overlap.
overlap=s.symbols("overlap",real=True)
observed=s.Integer(2)+2*overlap*s.cos(theta)
assert observed.subs(overlap,0)==2
assert s.simplify(observed.subs(overlap,1)-intensity)==0
print("PASS finite amplitude interference: 0 coherent, 2 incoherent for opposite phases")
print("PASS visibility under phase control and distinguishability / overlap gate")
print("UNPROVED: physical history action-to-phase, field propagator and NV ODMR coupling")
