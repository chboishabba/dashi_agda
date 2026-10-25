#!/usr/bin/env python3
"""Same-action centre-character selection gates for trinification 27.

Attribution: E6/trinification representations (Slansky 1981); source cubic
first-Tits implementation belongs to dashi_agda #1106, original rational
Albert formal witnesses to dashi_lean4 #52. Physical orbifold #1241
owns the quotient bundle/endpoint anomaly tests. This code only computes
necessary centre-invariance for tensor monomials; it NEVER asserts existence
of an invariant contraction or equivalence of Albert forms/physical actions.
"""
from itertools import product
from collections import Counter
W=((1,-1,0),(-1,0,1),(0,1,-1))
def c(w):return tuple(x%3 for x in w)
def add(*ws):return tuple(sum(w[j] for w in ws)%3 for j in range(3))
assert len({c(x) for x in W})==3
assert all(sum(w)==0 for w in W)
assert all(add(w,w,w)==(0,0,0) for w in W)
assert add(*W)==(0,0,0)
allowed=[]
for labels in product(range(3),repeat=3):
    if add(*(W[k] for k in labels))==(0,0,0):
        allowed.append(labels)
counts=Counter(tuple(sorted(v)) for v in allowed)
assert set(counts)=={(0,0,0),(1,1,1),(2,2,2),(0,1,2)}
assert [counts[x] for x in [(0,0,0),(1,1,1),(2,2,2),(0,1,2)]]==[1,1,1,6]
assert len(allowed)==9
# A diagonal centre element on the SU3^3 cover acts trivially
# on all 27 blocks, permitting the representation to descend.
for k in range(3):
    assert all(sum(w)*k%3==0 for w in W)
# Non-diagonal cover centre has a nontrivial action on at least one block.
for z in product(range(3), repeat=3):
    if len(set(z))>1:
        assert any(sum(w[j]*z[j] for j in range(3))%3 for w in W)
# Bilinear pairing with the contragredient has zero centre weight.
assert all(add(w,tuple(-x for x in w))==(0,0,0) for w in W)
print("PASS 27-source centre action descends iff cover-centre diagonal")
print("PASS cubic centre-allowed block triples = AAA BBB CCC and six ABC permutations")
print("PASS 27/27 finite ordered cubic block test, nine necessary candidates")
print("PASS dual diagonal bilinears have zero centre weight")
print("OPEN invariant contractions, original first-Tits cubic coefficients, same-action E6 gauge transport")
print("OPEN quotient global anomalies, spin/eta/CS5 and physical KK source")
