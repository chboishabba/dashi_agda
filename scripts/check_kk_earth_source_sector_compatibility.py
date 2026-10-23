#!/usr/bin/env python3
"""Constant-radius 5D product Einstein-equation sector consistency.
Signature (- + + + +); geometric units. Algebraic necessary condition, not full junction solution.
"""
import sympy as s
rho,p,F2,K,V=s.symbols("rho p F2 K V", real=True)
def residual(trace4,t55):return s.expand(t55-trace4/2)
assert residual(-rho+3*p,0)==(rho-3*p)/2
assert residual(0,-F2/4)==-F2/4
assert residual(-K-4*V,-K/2-V)==V
assert residual(0,0)==0
print("dust/no fifth pressure:",residual(-rho+3*p,0))
print("pure 4D Maxwell:",residual(0,-F2/4))
print("5D scalar/Higgs-like field depending on 4D:",residual(-K-4*V,-K/2-V))
print("PASS sector compatibility identities; neither generic EM nor Higgs potential automatically stabilizes circle")
