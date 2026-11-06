#!/usr/bin/env python3
"""Exact finite Wilson two-marked formal-jet BIDI reference.

The exhaustive three-state rational controls check the finite algebra
mirrored by YMClayOriginalWilsonFiniteTwoSourceJetExact.agda:
  [s t] log Z(s,t) = E(FG) - E(F) E(G)
for Z(s,t)=E((1+sF)(1+tG)).  They do NOT demonstrate analytic
differentiability of a continuous SU(N) Haar integral, CMP116 physical
localization, Agda kernel acceptance or any continuum result.
"""
from fractions import Fraction as Q
from itertools import product, permutations
import json

def expectation(weights, values):
    return sum((w * x for w, x in zip(weights, values)), Q(0)) / sum(weights)

def cov(weights, left, right):
    first = expectation(weights, left)
    second = expectation(weights, right)
    pair = expectation(weights, tuple(a * b for a, b in zip(left, right)))
    return pair - first * second

def formal_jet(weights, left, right):
    # Z(s,t)=1+s*Z_s+t*Z_t+s*t*Z_st:
    # the mixed logarithmic coefficient is Z_st-Z_s Z_t.
    zs = expectation(weights, left)
    zt = expectation(weights, right)
    zst = expectation(weights, tuple(a*b for a,b in zip(left,right)))
    return zst-zs*zt

def test():
    count = 0
    values = (-1,0,1)
    for raw_weight in product((1,2,3), repeat=3):
        weight = tuple(map(Q, raw_weight))
        for raw_left in product(values, repeat=3):
            left = tuple(map(Q,raw_left))
            for raw_right in product(values, repeat=3):
                right = tuple(map(Q,raw_right))
                direct = cov(weight, left, right)
                assert direct == formal_jet(weight,left,right)
                assert direct == cov(weight,right,left)
                count += 1
    # Same-source observable renaming must preserve the coefficient.
    w = tuple(map(Q,(1,2,3)))
    f = tuple(map(Q,(-1,0,1)))
    g = tuple(map(Q,(0,1,-1)))
    for order in permutations(range(3)):
        assert cov(w,f,g) == cov(tuple(w[i] for i in order),
            tuple(f[i] for i in order),tuple(g[i] for i in order))
    # Negative control: a changed normalized measure cannot be imported
    # as though it were the identical original Wilson source.
    left = right = tuple(map(Q,(0,1,0)))
    assert cov(w,left,right) == Q(2,9)
    assert cov(tuple(map(Q,(1,2,4))),left,right) == Q(10,49)
    assert cov(w,left,right) != cov(tuple(map(Q,(1,2,4))),left,right)
    return {"status":"PASS_EXACT_RATIONAL_REFERENCE",
        "exhaustive_three_state_cases":count,
        "same_source_relabelings":6,
        "changed_measure_negative_control":"REJECTED",
        "actual_SU_N_Haar_calculus":"NOT_TESTED",
        "CMP116_source_applicability":"NOT_TESTED",
        "agda_kernel":"NOT_TESTED"}

if __name__=="__main__":
    print(json.dumps(test(),indent=2))
