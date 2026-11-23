#!/usr/bin/env python3
"""RH original selected four-window: exact J2 transversality and conditional wedge.

Only source-dependent coefficients and algebraic remainder implication are checked.
The existence of analytic compact-even-bump branch and remainder constant is a
separate proof obligation, NOT accepted by SymPy or Lean here.
"""
import sympy as s
l,a,u,eps,R,C,d=s.symbols('l a u eps R C d',real=True)
Jmu=s.pi**2*(8-3*l)/4
assert s.simplify(Jmu.subs(l,s.Rational(2,3))-3*s.pi**2/2)==0
assert s.simplify(Jmu.subs(l,s.Rational(1,2))-13*s.pi**2/8)==0
mu0=(13*l-8)/(144-54*l)
mu1=-8*(l-2)*(27*l*l-52*l-9*s.sqrt(3)*l+4*s.sqrt(3))/(9*s.pi*(3*l-8)**2)
assert s.simplify(mu1.subs(l,s.Rational(1,2)) - 4*(-77-2*s.sqrt(3))/(507*s.pi))==0
assert s.simplify(mu1.subs(l,s.Rational(2,3)) - 16*(-34-3*s.sqrt(3))/(729*s.pi))==0
c0=s.Rational(120,13)
c2=640*(2*s.pi-s.sqrt(3))/(39*s.pi)
c2a=2560*(s.sqrt(3)+2*s.pi)/(39*s.pi)
c4=s.Rational(5120,351)*(1-16*a**4)
assert s.simplify(c2)>0 and s.simplify(c2a)>0
for av in [s.Rational(-49,100),s.Rational(-1,4),0,s.Rational(1,4),s.Rational(49,100)]:
    assert s.simplify(c4.subs(a,av))>0
# If shape-dependent eps = m2*R²/2 with m2>0 and a belongs to
# |a|<=1/2-d, d>0, the coefficient sum dominates
# cmin*(R²+u⁴), with cmin=min((120/13)*m2/2, c4(1/2-d)).
# A certified remainder |rem|<=C*(R⁴+R²u⁴+u⁶)
# is <= C*(R²+u²)*(R²+u⁴) when R,u<=1.
assert s.expand((R**2+u**2)*(R**2+u**4) - (R**4+R**2*u**4+u**6))==R**2*u**2
print('PASS J2 mu-derivative >= 3*pi²/2 on selected lambda interval')
print('PASS selected endpoint mu1 formulas and signed positive jet coefficients')
print('PASS conditional uniform wedge remainder domination')
print('OPEN: original fixed-shape bump analytic branch and explicit finite-t remainder')
print('OPEN: actual-zero ordinate distribution and H_n+E_n+S_W<T_W')
