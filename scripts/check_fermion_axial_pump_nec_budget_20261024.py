#!/usr/bin/env python3
"""Adversarial FREE 1+1D massless Dirac thermodynamic NEC test.

q complex Dirac species; fixed NS negative circle vacuum and two opposite
chiral Fock excitations. Chemical potential continuum approximation, not
exact finite-circle discrete occupancy or the curved 4D spin-c Dirac state.
"""
import sympy as s
q,L,mu=s.symbols('q L mu',real=True,positive=True)
casimir=-s.pi*q/(6*L**2)
# Each chiral branch has positive Fock energy ∫0^mu eps d eps/(2pi).
excitation=q*(mu**2+mu**2)/(4*s.pi)
rho=casimir+excitation
p_r=rho
NEC=rho+p_r
assert s.simplify(s.diff(NEC,mu)-2*q*mu/s.pi)==0
threshold=s.pi/(s.sqrt(3)*L)
assert s.simplify(NEC.subs(mu,threshold))==0
assert s.simplify(NEC.subs(mu,2*threshold))>0
assert s.simplify(NEC.subs(mu,0))<0
print('PASS: axial Fock excitations raise radial NEC versus NS vacuum')
print('PASS: formal continuum zero at mu*L=pi/sqrt(3), q-independent')
print('WARNING: threshold is in discrete finite-circle level regime; not an exact finite-size transition')
print('OPEN: driven renormalized 4D Dirac state including anomaly and backreaction')
