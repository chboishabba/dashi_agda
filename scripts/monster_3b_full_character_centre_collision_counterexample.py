#!/usr/bin/env python3
"""Genuine finite group C2 x C3 x C3: same tested centre, distinct FULL characters.

Finite verification counterexample only. Not a 6.Suz/Monster identity or receipt.
Character values use exact Z[zeta3] = {(a,b): a+b*zeta}; zeta^2=-1-zeta.
Source mathematical roots: finite-group character orthogonality and Fourier
characters (Serre, 1977; Terras, 1999). No Monster primary sources claimed.
"""
from itertools import product
import json

Z=((1,0),(0,1),(-1,-1))
def mul(x,y):
    a,b=x;c,d=y
    return (a*c-b*d,a*d+b*c-b*d)
def add(*xs):return tuple(sum(x[i] for x in xs) for i in range(2))
def scale(n,x):return (n*x[0],n*x[1])
def character(sign, phase_main, phase_extra, g):
    t,a,b=g
    return scale((-1 if sign and t else 1),
                 mul(Z[(phase_main*a)%3],Z[(phase_extra*b)%3]))

def run():
    G=list(product(range(2),range(3),range(3)))
    assert len(G)==18
    center_c2=(1,0,0)
    center_c3=(0,1,0)
    aux=(0,0,1)
    # Two honest degree-78 representations with identical C2 and main C3
    # traces, but different at aux C3. At identity both have degree 78.
    u=lambda g:scale(78,character(False,1,0,g))
    v=lambda g:scale(78,character(False,1,1,g))
    for g in [(0,0,0),center_c2,center_c3,(0,2,0)]:
        assert u(g)==v(g)
    assert u(aux)!=v(aux)
    W=lambda g:scale(12,character(True,1,0,g))
    au=lambda g:add(W(g),u(g))
    av=lambda g:add(W(g),v(g))
    assert all(au(g)==av(g) for g in [(0,0,0),center_c2,center_c3,(0,2,0)])
    assert au(aux)!=av(aux)
    assert au(center_c2)==av(center_c2)==(66,0)
    assert au(center_c3)==av(center_c3)==scale(90,Z[1])
    assert sum(int(au(g)!=av(g)) for g in G)>0
    # Exact character orthogonality using genuine finite-group elements.
    def inverse(x):return (x[0],(-x[1])%3,(-x[2])%3)
    for f,h,expected in ((u,u,78*78),(u,v,0),(v,v,78*78)):
        value=add(*(mul(f(g),h(inverse(g))) for g in G))
        assert value==(18*expected,0)
    return {"status":"PASS", "group":"C2 x C3 x C3", "order":18,
        "same_identity_C2_and_central_C3_characters":True,
        "first_character_difference_at_extra_C3":{
            "g":"(0,0,1)","module_u":u(aux),"module_v":v(aux)},
        "degree90_C2_trace":list(au(center_c2)),
        "degree90_main_C3_trace":list(au(center_c3)),
        "full_class_functions_equal":False,
        "genuine_finite_group_characters_not_fabricated_rows":True,
        "actual_Monster_78_identification":False,"GAP_executed":False}
if __name__=='__main__':
    print(json.dumps(run(),indent=2))
