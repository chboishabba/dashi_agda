#!/usr/bin/env python3
"""Exact effective-fluid Einstein/Israel RN junction and ADM mass identities.

This is a GR matching theorem for an ASSUMED conserved source; it does not
construct a global charged-fermion quantum state, full 4D determinant, or a
physical device. Standard Israel/Darmois matching and Misner-Sharp mass math.
"""
import sympy as sp

r,v,F,Q,P,rpp,E=sp.symbols('r v F Q P rpp E',nonzero=True,real=True)
M=r/sp.Integer(2)*(1+Q**2/r**2-v**2)
f=sp.factor(1-2*M/r+Q**2/r**2)
assert sp.simplify(f-v*v)==0
Phi_RN=sp.factor((M/r**2-Q**2/r**3)/v)
C=v*v-1+2*r*v*F+Q*Q/r**2-2*P
F_on_constraint=sp.solve(C,F)[0]
assert sp.factor((F_on_constraint-Phi_RN)-P/(r*v))==0
# M'(x)=r'(x)*E(x) from the same tt Einstein equation.
# E=the integrated-over-sphere quantum density (4pi r² rho).
rpp_on_tt=sp.solve(1-v*v-2*r*rpp-Q**2/r**2-2*E,rpp)[0]
Mprime=sp.diff(M,r)*v+sp.diff(M,v)*rpp
assert sp.simplify(Mprime.subs(rpp,rpp_on_tt)-v*E)==0
print('PASS: f_RN=rprime², Ktt jump=P/(r*rprime) on constraint')
print('PASS: dM/dx=rprime E. At P=0, rprime!=0, the classical Israel shell vanishes.')
print('NOT PROVED: Dirac quantum state globally generates abrupt source transition.')
