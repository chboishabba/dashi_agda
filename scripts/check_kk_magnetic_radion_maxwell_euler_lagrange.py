#!/usr/bin/env python3
"""Exact KK Maxwell/radion EL equations in 1D magnetic field ansatz.
Assumes standard 5D->4D Jordan action; g4 flat only for the restricted
A_y(x), phi(x) Euler-Lagrange calculation.
Does not assert flat g4 solves the complete metric equations.
"""
import sympy as s

x,k=s.symbols('x k',real=True,nonzero=True)
p=s.Function('phi')(x)
a=s.Function('a')(x)
R4=s.Symbol('R4')
# F_xy=a'(x), F^2=2a'^2 on Minkowski base.
F2=2*s.diff(a,x)**2
L=p*R4-s.Rational(1,4)*k**2*p**3*F2
Ephi=s.factor(s.diff(L,p)-s.diff(s.diff(L,s.diff(p,x)),x))
Ea=s.factor(s.diff(L,a)-s.diff(s.diff(L,s.diff(a,x)),x))
assert s.simplify(Ephi-(R4-s.Rational(3,2)*k**2*p**2*s.diff(a,x)**2))==0
assert s.simplify(Ea-k**2*s.diff(p**3*s.diff(a,x),x))==0
# In the linear magnetic potential a(x)=b*x, the Maxwell EOM needs
# 3 k² b phi² phi'=0, excluding a variable phi for nonzero b,phi.
b=s.symbols('b',real=True,nonzero=True)
linear=s.factor(Ea.subs({s.diff(a,x,2):0,s.diff(a,x):b}))
assert s.simplify(linear-3*k**2*b*p**2*s.diff(p,x))==0
# Constant radius and R4=0 under trace => radion requires b=0.
const=s.factor(Ephi.subs({R4:0,s.diff(a,x):b}))
assert s.simplify(const+s.Rational(3,2)*k**2*p**2*b*b)==0
print('PASS variation: E_phi=R4-3*k² phi² (a_x)²/2')
print('PASS variation: E_A=k² d_x(phi³ a_x)')
print('PASS nonzero constant B and variable phi conflict with source-free Maxwell')
print('PASS flat-base constant-radius nonzero B conflicts with radion equation')
print('LIMIT: restricted-action Euler-Lagrange; general 5D tensor identity assumed')
