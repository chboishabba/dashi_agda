#!/usr/bin/env python3
"""Linear massive-radion sourced sphere: exact interior/exterior matching.
Not a complete 5D Einstein/matter source, metric backreaction, or Earth fit.
"""
import sympy as s
r,R,m,S=s.symbols('r R m S',positive=True)
A=-S*(R*m+1)*s.exp(-R*m)/m**3
B=S*(R*m*s.cosh(R*m)-s.sinh(R*m))/m**3
inside=S/m**2+A*s.sinh(m*r)/r
outside=B*s.exp(-m*r)/r
op=lambda f:s.diff(f,r,2)+2*s.diff(f,r)/r-m**2*f
assert s.simplify(op(inside)+S)==0
assert s.simplify(op(outside))==0
assert s.simplify(inside.subs(r,R)-outside.subs(r,R))==0
assert s.simplify(s.diff(inside,r).subs(r,R)-s.diff(outside,r).subs(r,R))==0
assert s.limit(inside,r,0).is_finite
assert s.limit(outside,r,s.oo)==0
print("PASS sourced Helmholtz, exterior, C1 matching, center regularity, asymptotic decay")
print("NO full 5D stress/Einstein or terrestrial matching")
