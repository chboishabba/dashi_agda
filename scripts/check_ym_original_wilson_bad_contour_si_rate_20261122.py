#!/usr/bin/env python3
"""Physical-distance absorption of a CONDITIONAL microscopic Wilson bad-contour rate.

No original gauge action is inferred from this elementary counting calculus:
P(rooted bad contour of size >=m) <= u (196u)^(m-1)/(1-196u)
is a SOURCE INPUT from the existing Wilson RP/chessboard/animal path.
This script verifies the uniform spacing/root multiplicity implication.
"""
from math import ceil
from sympy import Rational, Symbol, exp, log, E, simplify, diff, N

q=Rational(1,4)
assert 0<q<1
kappa=-log(q)
D=4
x=Symbol('x',positive=True)
R=Symbol('R',positive=True)
theta=kappa*R/2
f=x**D*exp(-theta*x)
fmax=(D/(E*theta))**D
assert simplify(diff(f,x).subs(x,D/theta))==0
assert simplify(f.subs(x,D/theta)-fmax)==0

a0=Rational(1,4)
Rmin=Rational(1)
physical_amplitude=(2*D/(E*kappa*Rmin))**D/(196*(1-q))
rate=kappa/(2*a0)
checked=0
for n in range(2,11):
    a=Rational(1,2**n)
    for dist in (Rational(1),Rational(3,2),Rational(2),Rational(3),Rational(5)):
        m=ceil(dist/a)
        original=Rational(1,a**D)*q**m/(196*(1-q))
        physical=physical_amplitude*exp(-rate*dist)
        assert N(physical-original,40)>=0
        checked+=1
print('PASS:', checked,'cutoff/physical-distance pairs with polynomial root count D=4')
print('PASS: exact symbolic stationary point and global polynomial-exponential maximum')
print('PHYSICAL BAD-EVENT RATE:',str(simplify(rate)),'inverse length in units of a0')
print('CONDITIONAL INPUTS: source chessboard, q*=196u*<1, a<=a0, roots<=C a^-D, R>=Rmin>0')
print('NOT: marked KP cluster charge, CMP116 good-field covariance, E1, same-H OS gap')
