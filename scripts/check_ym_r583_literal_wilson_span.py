#!/usr/bin/env python3
"""Exact rational finite control for R583 source-native Wilson span algebra.

This tests the finite list/ring identities, NOT the original physical SU(N)
Wilson Gibbs system, CMP119 analytic moments, H1 clustering or OS4.
"""
from fractions import Fraction as F
from itertools import product
import json

weights={"x":(F(2,3),F(-1,2)),"y":(F(-1,3),F(3,4))}
words=[(),("x",),("y",),("x","y")]
terms=[(a,w) for a in (F(-1),F(0),F(1),F(1,2)) for w in words]
spans=[()]+[(t,) for t in terms]+[(a,b) for a in terms for b in terms if a[0] and b[0]][:140]

def word_value(word,config):
    v=F(1)
    for symbol in word:
        v*=weights[symbol][config]
    return v

def embed(span,config):
    return sum((a*word_value(w,config) for a,w in span),F(0))

def scale(k,span):
    return tuple((k*a,w) for a,w in span)

def mul(left,right):
    return tuple((a*b,u+v) for a,u in left for b,v in right)

checks=0
for s in spans:
    for config in range(2):
        assert embed((),config)==0
        assert embed(scale(F(2,3),s),config)==F(2,3)*embed(s,config)
        checks+=2
for s,t in product(spans,repeat=2):
    for config in range(2):
        assert embed(s+t,config)==embed(s,config)+embed(t,config)
        assert embed(mul(s,t),config)==embed(s,config)*embed(t,config)
        checks+=2
print(json.dumps({
    "result":"PASS",
    "exact_fraction_checks":checks,
    "finite_spans":len(spans),
    "configurations":2,
    "actual_SU_N_Wilson_CMP119_H1_OS4_proved":False
},indent=2))
