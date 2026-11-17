#!/usr/bin/env python3
"""Bishop Machin period algebra independent exact polynomial checks.

This validates ONLY the algebraic 4*quarter-angle step. The still-open
analytic Agda theorems must identify the actual Bishop sine/cosine series
with the quarter-angle rational Machin tangent and prove addition laws.
No statement about an Agda or Lean kernel is implied.
"""
import sympy as sp
s,c=sp.symbols("s c", real=True)
sin2=2*s*c
cos2=c*c-s*s
sin4=2*sin2*cos2
cos4=cos2*cos2-sin2*sin2
assert sp.expand(sin2.subs(c,s) - (s*s+c*c).subs(c,s))==0
assert sp.expand(cos2.subs(c,s))==0
assert sp.expand(sin4.subs(c,s))==0
assert sp.expand(cos4+1).subs(c,s).factor()==-(2*s*s-1)*(2*s*s+1)
# On s=c and s^2+c^2=1, s^2=1/2.
assert sp.expand((cos4+1).subs(c,s).subs(s*s,sp.Rational(1,2)))==0
# Prove a stronger polynomial identity before quotient reduction:
assert sp.factor(cos4+1 - (1-(s*s+c*c)**2))==0
# Pi Machin arithmetic is an independent source: zeta above concerns trig only.
print("BISHOP_MACHIN_FOUR_ANGLE_ALGEBRA_PASS=6")
