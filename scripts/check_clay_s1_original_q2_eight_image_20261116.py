#!/usr/bin/env python3
"""Exact original eight Q2 local Kummer image arithmetic regression.
The cardinality bound 8 is from standard local elliptic group structure,
not a finite search. Native Agda/Lean same-object H1 remains unproved.
"""
from fractions import Fraction as F

def cls(a):
    assert a
    n,d=a.numerator,a.denominator
    def peel(k):
        e=0
        while k%2==0:k//=2;e+=1
        return e,k
    en,u=peel(abs(n));ed,v=peel(d)
    return ((en-ed)%2,((1 if n>0 else -1)*u*pow(v,-1,8))%8)

xs=[F(x) for x in (28,31,33,39,41,112)]+[F(1,4),F(1,16)]
expected=[
 ((0,7),(0,3),(0,5)),
 ((0,7),(1,7),(1,1)),
 ((0,1),(1,1),(1,1)),
 ((0,7),(1,3),(1,5)),
 ((0,1),(1,5),(1,5)),
 ((0,7),(0,7),(0,1)),
 ((0,1),(0,5),(0,5)),
 ((0,1),(0,1),(0,1)),
]
triples=[tuple(cls(z) for z in (x,x-1,x+1)) for x in xs]
assert triples==expected
assert len(set(triples))==8
for t in triples:
    assert sum(a[0] for a in t)%2==0
    p=1
    for a in t:p=p*a[1]%8
    assert p==1
# Original Hensel witnesses: x^3-x = scale^2 * u, u =1 mod 8.
scales=[F(2),F(8),F(8),F(4),F(4),F(4),F(1,8),F(1,64)]
units=[5481,465,561,3705,4305,87801,-15,-255]
for x,scale,u in zip(xs,scales,units):
    assert x**3-x==scale**2*u and u%8==1
# Local group index: 2^[K:Q2]*|E(K)[2]| = 2*4 =8.
assert 2**1*4==len(set(triples))
print('PASS 8/8 original Q2 point Hensel factor certificates')
print('PASS 8 distinct full square-class Kummer triples')
print('PASS triple product square-class identity, 8/8')
print('CLASSICAL THEOREM: |E(Q2)/2E(Q2)|=8; exhaustive by index')
print('FIREWALL native cohomology realization OPEN; S3/S5/S6 OPEN')
