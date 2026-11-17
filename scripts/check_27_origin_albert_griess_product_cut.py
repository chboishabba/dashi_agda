#!/usr/bin/env python3
"""Source-exact finite multiplication control: Griess 1990 homogeneous Albert.
Reuses formula from dashi_lean4 PR #52; this is NOT Monster VOA or graph L.
"""
from fractions import Fraction as F
from itertools import product

V=tuple(product(range(3),repeat=3)); o=(0,0,0)
def add(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def neg(a):return tuple((-x)%3 for x in a)
def independent(x,y):
    return x!=o and not any(all((k*u-v)%3==0 for u,v in zip(x,y)) for k in range(3))
def g(x,y):
    a,b,c=x;p,q,r=y
    return (-a*b*r-c*p*q+b*c*p+a*q*r)%3
omega=((F(1),F(0)),(F(0),F(1)),(F(-1),F(-1)))
def mul(x,y):
    c = F(-1,2) if independent(x,y) else F(1)
    return add(x,y), tuple(c*z for z in omega[g(x,y)])

assert len(V)==27
assert all(mul(o,x)==(x,(F(1),F(0))) for x in V)
assert all(mul(x,neg(x))==(o,(F(1),F(0))) for x in V)
nonzero=tuple(x for x in V if x!=o)
assert len(nonzero)==26
assert len({frozenset((x,neg(x))) for x in nonzero})==13
for a in nonzero:
    assert mul(a,o)==(a,(F(1),F(0)))
    assert mul(a,neg(a))==(o,(F(1),F(0)))
    assert mul(a,a)==(neg(a),(F(1),F(0)))
print('PASS Griess 1990 homogeneous Albert: e0 unit; 26 nonzero labels; 13 antipodal pairs')
print('PASS for each nonzero a: e_a*e_-a=e0, e_a*e0=e_a, e_a^2=e_-a')
print('NO-GO the 26 non-unit homogeneous grade span is not a Jordan ideal/subalgebra')
print('BOUNDARY line/vector coordinates are complex Q(omega) and NON-spatial F3^3 characters')
print('BOUNDARY this does not match the open path P3^3 Laplacian or physical bosonic 26D target')
