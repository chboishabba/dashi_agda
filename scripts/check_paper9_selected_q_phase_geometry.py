#!/usr/bin/env python3
"""Exact CM phase/scale and reciprocal Möbius geometry.

Classical complex exponential simplification is a *reference*, NOT a proof
of Bishop original Machin/Cayley phase evaluation. No analytic CM j claim.
"""
import json
from sympy import symbols, sqrt, I, Rational, diff, simplify, series, exp, pi, expand

def zero(expr):
    v=simplify(expand(expr))
    assert v==0, str(v)

r=sqrt(163)
tau=(-1+I*r)/2
p=symbols('p', positive=True)
w=symbols('w')
# Original Machin pi is independent of prepackaged transcendental pi.
half=p*r/2
full=p*r
zero(2*half-full)

f=lambda z:-41/(z+1)
g=lambda z:(-41-z)/z
alpha=(-81-I*r)/82
beta=(-81+I*r)/82
zero(f(tau)-tau);zero(g(tau)-tau)
zero(diff(f(w),w).subs(w,tau)-alpha)
zero(diff(g(w),w).subs(w,tau)-beta)
zero(alpha*beta-1)
zero(alpha+beta+Rational(81,41))
# Exact q-ray coefficient pullback; no analytic existence assumption.
a,b=symbols('a b')  # original q-Euler first and second j jets
u=-2*full*w/(1-w)
# formal exp pullback by Euler coordinate t=log(q/q0):
# j(q0 exp(t))=j0+a*t+(b/2)*t^2 + O(t^3)
formal=a*u+b*u*u/2
A=simplify(diff(formal,w).subs(w,0))
B=simplify(diff(formal,w,2).subs(w,0)/2)
zero(A+2*full*a)
zero(B+2*full*a-2*full**2*b)
qgeom=series(exp(u),w,0,3).removeO()
zero(qgeom-(1-2*full*w+(2*full**2-2*full)*w*w))
# Classical exp result is inspected separately and is NOT promoted.
classical_phase=simplify(exp(2*pi*I*tau)/(-exp(-pi*r)))
zero(classical_phase-1)
# Classical q Euler coordinate, not a Bishop proof.
assert simplify(diff(exp(2*pi*I*w),w)/(2*pi*I*exp(2*pi*I*w))-1)==0
print(json.dumps({'cm_quadratic':True,'reciprocal_fixed_points':2,
 'mobius_derivative_multipliers':2,'reciprocal_multiplier_and_trace':2,
 'machin_half_to_disk_full_scale':True,'q_log_pullback_first_second_coefficients':2,
 'formal_exponential_ray_coefficients':3,'classical_phase_reference_only':True,
 'bishop_same_object_phase_proved':False,'analytic_cm_root_proved':False}, sort_keys=True))
