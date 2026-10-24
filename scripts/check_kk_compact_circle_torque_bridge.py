#!/usr/bin/env python3
"""Compact S1 KK Fourier spectrum and gauge shift fixture; no physical R determination."""
import sympy as s
theta,R,k=s.symbols("theta R k",positive=True,real=True)
mode=s.exp(s.I*k*theta)
assert s.simplify(-s.diff(mode,theta,2)/R**2-k**2*mode/R**2)==0
y,A,dchi,kappa=s.symbols("y A dchi kappa",nonzero=True,real=True)
assert s.expand((y-dchi)+kappa*(A+dchi/kappa)-(y+kappa*A))==0
# Rotational SO(3) orbital torque and internal circle derivative are different tangent directions.
print("PASS S1 Laplacian: eigenvalue n²/R² for integer n")
print("PASS KK local fibre-gauge shift")
print("Note angular momentum torque in SO(3) not equal to winding/momentum on S1")
