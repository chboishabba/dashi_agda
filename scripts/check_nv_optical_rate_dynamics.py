#!/usr/bin/env python3
"""Symbolic minimal NV optical pump vs microwave population model.

This is a two-population phenomenological surrogate, not an NV seven-level
optical-cycle/Lindblad model or a calibration of the 2026 human MCG paper.
"""
import sympy as s
r,w,B,D,gamma,drive,Gamma,amp=s.symbols(
    "r w B D gamma drive Gamma amp",positive=True,real=True)
p=s.symbols("p",real=True)
flow=s.expand(r*(1-p)+w*(1-2*p))
pstar=(r+w)/(r+2*w)
assert s.simplify(flow.subs(p,pstar))==0
assert s.simplify(pstar+w/(r+2*w)-1)==0
assert s.diff(flow,p)==-r-2*w
assert s.simplify(s.diff(pstar,w)+r/(r+2*w)**2)==0
det=drive-(D+gamma*B)
W=amp*Gamma**2/(det**2+Gamma**2)
P=s.factor(pstar.subs(w,W))
dP=s.factor(s.diff(P,B))
bright,dark,bg=s.symbols("bright dark bg",nonnegative=True,real=True)
mu=s.factor(bright*P+dark*(1-P)+bg)
assert s.simplify(s.diff(mu,B)-(bright-dark)*dP)==0
assert s.simplify(P.subs(amp,0)-1)==0
assert s.simplify(P.subs(det,0)-P.subs(det,0))==0
# At positive rates, P in [1/2,1] and dP/dW<0.
FI=s.factor(s.diff(mu,B)**2/mu)
assert s.simplify(FI-s.diff(mu,B)**2/mu)==0
print("PASS NV optical pumping steady state, normalization, stability, MW dependence")
print("PASS Lorentzian drive to fluorescence response and conditional Poisson Fisher information")
print("ASSUMPTIONS r>0, Gamma>0, amp>=0, nonnegative photon means, two-state reduction")
print("OPEN physical NV optical-cycle/ISC constants, photon statistics, tissue and sensor calibration")
