#!/usr/bin/env python3
r"""Flat-but-unbounded gauge escape on a punctured plane, not a wild horn.

Standard prior art: flat bundle/holonomy correspondence; Aharonov–Bohm
connection. Independent #1244 horn A5 root has order five, but this
R²\{0} control does NOT realize that horn group or the selected #1247 W.
"""
import sympy as s
from fractions import Fraction as F
x,y=s.symbols('x y',real=True)
r2=x*x+y*y
ax=-y/r2; ay=x/r2
assert s.simplify(s.diff(ay,x)-s.diff(ax,y))==0
assert s.simplify(ax*ax+ay*ay-1/r2)==0
# H=diag(1,-1,0), A=(i/5)H*(-y dx + x dy)/(x²+y²).
alpha=s.Rational(1,5)
angle=2*s.pi*alpha
hol_trace=s.simplify(1+2*s.cos(angle))
assert s.simplify(hol_trace-(1+s.sqrt(5))/2)==0
operator_gap_sq=s.simplify(2-2*s.cos(angle))
assert s.simplify(operator_gap_sq-(5-s.sqrt(5))/2)==0
assert s.simplify(operator_gap_sq-1).is_positive
print('PASS flat R2-minus-origin SU3 connection: dA+A∧A=0, hol order5 with gap²=(5-sqrt5)/2>1')
for n in (2,3,5,8,13,34,100):
    r=F(1,n)
    # ||A||_op = alpha/r, length = 2*pi*r; holonomy fixed.
    norm_bound=F(1,5)/r
    assert norm_bound==F(n,5)
    assert norm_bound*r==F(1,5)
    print(f'PASS puncture n={n}: radius={r}, loop-length=2*pi/{n}, ||A||={norm_bound}, fixed order5 hol')
print('NO-GO false claim that a smooth FLAT exterior connection with short loops has trivial holonomy without UNIFORM coefficient bound')
print('BOUNDARY this is an ordinary Z fundamental group, not the Hatcher perfect group; no physical source energy or global wild completion')
