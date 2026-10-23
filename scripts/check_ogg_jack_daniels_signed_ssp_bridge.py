#!/usr/bin/env python3
"""Exact Jack Daniels / Ogg prime-support and signed SSP counterexample donor.
Arithmetic only: Ogg's genus-zero primes, Monster group order support,
FRACTRAN signed valuations, and 47*59*71 = 196883.
This does not construct Monster representations, McKay–Thompson functions,
or any physical gravitational action.
"""
from math import prod
from fractions import Fraction

OGG=(2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)
MONSTER_ORDER=808017424794512875886459904961710757005754368000000000
assert all(MONSTER_ORDER%p==0 for p in OGG)
n=MONSTER_ORDER
exponents={}
for p in OGG:
    k=0
    while n%p==0:
        k+=1;n//=p
    exponents[p]=k
assert n==1 and set(exponents)==set(OGG)
assert prod(p**k for p,k in exponents.items())==MONSTER_ORDER
assert 47*59*71==196883
assert 196883+1==196884

def valuation(x,p):
    if x==0: raise ValueError("zero has no finite prime valuation")
    a,b=x.numerator,x.denominator
    def vp(n):
        c=0
        while n%p==0: n//=p;c+=1
        return c
    return vp(a)-vp(b)

# Signed exponents include negative denominators. They do not become
# Monster power maps simply from matching numerical prime support.
f=Fraction(47*59,23*7)
v={p:valuation(f,p) for p in sorted(set(OGG)|{23})}
assert v[47]==v[59]==1 and v[23]==v[7]==-1
assert valuation(1/f,47)==-valuation(f,47)
assert valuation(1/f,23)==-valuation(f,23)
assert 47%23 and 59%7 and 71%11
print("PASS full prime factorisation of Monster order uses exactly Ogg SSP15")
print("PASS 47*59*71=196883 and 196884=196883+1")
print("PASS signed FRACTRAN reciprocal negates prime valuations")
print("NO PROMOTION: numerical factor matching does not define a Monster power map, braid action, or KK charge")
