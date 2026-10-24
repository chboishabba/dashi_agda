#!/usr/bin/env python3
"""Source-identity F81/F9 quadratic-tower arithmetic, not a Monster/physics test.

Original F81 quartic/multiplication: iit_jfine_selected_punctured79_audit.py
Original F9-shaped Frobenius owner: OggSSPP3F9FrobeniusCandidateNoGoExact
DASHI-derived chosen coordinates gamma=(0,1,2,2), beta=(0,0,1,1).
Checks all 81 states and every ordered pair (6561) of field operations.
"""
from __future__ import annotations
from itertools import product
from hashlib import sha256
import json
from iit_jfine_selected_punctured79_audit import ZERO, ONE, add, multiply, power

GAMMA=(0,1,2,2)
BETA=(0,0,1,1)
DELTA=add(ONE,GAMMA)
COORDS=tuple(product(range(3),repeat=4))

def scalar(k):
    return (k%3,0,0,0)

def embed(v):
    a0,a1,b0,b1=v
    a=add(scalar(a0),multiply(scalar(a1),GAMMA))
    b=add(scalar(b0),multiply(scalar(b1),GAMMA))
    return add(a,multiply(b,BETA))

def plus9(a,b):
    return tuple((x+y)%3 for x,y in zip(a,b))

def mul9(a,b):
    a0,a1=a; b0,b1=b
    return ((a0*b0-a1*b1)%3,(a0*b1+a1*b0)%3)

def neg9(a):
    return tuple((-x)%3 for x in a)

def tower_add(v,w):
    return tuple((x+y)%3 for x,y in zip(v,w))

def tower_mul(v,w):
    a,b=v[:2],v[2:]
    c,d=w[:2],w[2:]
    return (plus9(mul9(a,c),mul9((1,1),mul9(b,d)))
            +plus9(mul9(a,d),mul9(b,c)))

def audit():
    assert multiply(GAMMA,GAMMA)==(2,0,0,0)
    assert multiply(BETA,BETA)==DELTA
    assert power(GAMMA,9)==GAMMA
    assert power(BETA,9)!=BETA

    representatives={v:embed(v) for v in COORDS}
    assert len(set(representatives.values()))==81
    assert representatives[(1,0,0,0)]==ONE
    for v,w in product(COORDS,repeat=2):
        assert embed(tower_add(v,w))==add(representatives[v],representatives[w])
        assert embed(tower_mul(v,w))==multiply(representatives[v],representatives[w])
    for v in COORDS:
        a,b=v[:2],v[2:]
        conjugate=a+neg9(b)
        assert embed(conjugate)==power(embed(v),9)
        norm=plus9(mul9(a,a),neg9(mul9((1,1),mul9(b,b))))
        assert embed(norm+(0,0))==power(embed(v),10)

    f9={embed((a,b,0,0)) for a,b in product(range(3),repeat=2)}
    assert f9=={x for x in representatives.values() if power(x,9)==x}
    report={
        "contract":"iit_f81_f9_same_object_quadratic_tower_arithmetic",
        "original_polynomial":"X^4+X+2 over F3",
        "gamma_source_coefficients":GAMMA,
        "beta_source_coefficients":BETA,
        "gamma_squared":"-1",
        "beta_squared":"1+gamma",
        "chosen_tower":"F9[beta]/(beta^2-1-gamma), F9=F3[gamma]/(gamma^2+1)",
        "field_elements_bijectively_mapped":81,
        "ordered_pairs_addition_checked":6561,
        "ordered_pairs_multiplication_checked":6561,
        "F9_same_subfield_as_original_quartic":True,
        "relative_Frobenius_9_equals_tower_conjugation":True,
        "relative_norm_10_equals_tower_norm":True,
        "classical_supersingular_moduli_identification":False,
        "Monster_action_identification":False,
        "Agda_kernel_receipt":False
    }
    report["payload_sha256"]=sha256(json.dumps(report,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    return report

if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
