#!/usr/bin/env python3
"""Exact finite/symbolic regression for RH→G2 cosh collapse; not an RH proof."""
import sympy as sp

u, q, multiplicity, displacement, ordinate, target = sp.symbols(
    'u q multiplicity displacement ordinate target', real=True)
original = 4*q*multiplicity*sp.cosh(displacement*u)*sp.cos((ordinate-target)*u)
collapsed = 4*q*multiplicity*sp.cos((ordinate-target)*u)
assert sp.simplify(original.subs(displacement, 0) - collapsed) == 0
for qsign, expected in [(1,8),(-1,-8)]:
    integral = sp.integrate(collapsed.subs({q:qsign,multiplicity:1,ordinate:0,target:0}),(u,-1,1))
    assert integral == expected, (qsign,integral)
print('PASS original G2 cosh collapses identically at horizontal offset 0')
print('PASS no signed cancellation: chosen collapsed integrals +8 and -8')
