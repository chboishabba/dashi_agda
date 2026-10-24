#!/usr/bin/env python3
"""Boosted KK source/matter-frame weak-field audit: algebra only, no Earth claim."""
import sympy as s
M,q,x,beta=s.symbols('M q x beta',real=True)
F=1-2*M*x;H=1+2*M*q*x
ett=-F/s.sqrt(H);err=s.sqrt(H)/F
assert s.simplify(s.diff(ett,x).subs(x,0)-M*(2+q))==0
assert s.simplify(s.diff(err,x).subs(x,0)-M*(2+q))==0
assert s.simplify(s.diff(err,x).subs(x,0)/s.diff(ett,x).subs(x,0)-1)==0
assert s.simplify(s.diff(H,x).subs(x,0)-2*M*q)==0
ptt=H**beta*ett;prr=H**beta*err
A=s.simplify(s.diff(ptt,x).subs(x,0));B=s.simplify(s.diff(prr,x).subs(x,0))
gamma=s.factor(B/A)
assert s.simplify(gamma-(2+q+2*beta*q)/(2+q-2*beta*q))==0
assert s.simplify(gamma.subs(beta,0)-1)==0
print('PASS Einstein-frame gamma=1 for this exterior and neutral Einstein matter coupling')
print('PASS radion charge proportional to M*q')
print('PASS generalized physical conformal coupling gamma=',gamma)
print('No Earth-source match, no actual PPN bound; distinct formulations require distinct matching.')
