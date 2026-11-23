#!/usr/bin/env python3
"""Original RH atomic real-q fourth-difference coercivity (NOT ζ-side).

Exact mathematical proof for d=dist(q,4Z) in [0,2]:
  -F(q)=(320/351)sin(pi*d/4)^4
  (20/351)d^4 <= -F(q) <= (5*pi^4/1404)d^4
by concavity sin(x)>=2x/pi, sin(x)<=x on [0,pi/2].
q-smoothing is NOT the original finite-R angular bump smoothing.
"""
import sympy as s
q,x=s.symbols('q x',real=True)
F=lambda z:-s.Rational(320,351)*s.sin(s.pi*z/4)**4
assert s.trigsimp(s.expand_trig(s.cos(2*x)-1)+2*s.sin(x)**2)==0
series=s.series(F(4+x),x,0,8).removeO().expand()
assert series.coeff(x,4)==-5*s.pi**4/1404
assert series.coeff(x,6)==5*s.pi**6/33696
assert s.Rational(320,351)/16==s.Rational(20,351)
assert s.simplify(s.Rational(320,351)*(s.pi/4)**4)==5*s.pi**4/1404
for i in range(-1200,1201):
    z=i/73
    d=min(abs(z-4*n) for n in range(-8,9))
    if d>2:continue
    a=float(-F(z))
    assert a+1e-11>=float(s.Rational(20,351))*d**4
    assert a<=float(5*s.pi**4/1404)*d**4+1e-11
for d in (s.Rational(1,4),s.Rational(1,2),s.Rational(1),s.Rational(2)):
    # centered positive q-bump with weights 1/4,1/2,1/4
    m=-(F(4-d)+2*F(4)+F(4+d))/4
    assert s.N(m)>0
    assert s.N(m-s.Rational(20,351)*d**4/2)>=0
print("PASS original RH real-q 4-periodic fourth-difference and exact fourth/sixth jet")
print("PASS global distance(q,4Z)^4 analytic sandwich with 2401 grid probes")
print("PASS strictly negative q-smoothed atomic notch for nontrivial positive bump")
print("OPEN W(R,t) finite-pole same-source analytic, zeta/μ/FarExact A2")
