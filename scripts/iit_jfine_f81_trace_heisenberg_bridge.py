#!/usr/bin/env python3
"""Construct exact F81 trace-dual pairing for source jFine four-trit shells.

Same polynomial as the existing iit_jfine_selected_punctured79_audit:
K=F3[X]/(X^4+X+2). H4 has two K-coordinate blocks and central F3.
All 81^2 ordered dot/trace comparisons are checked. This is a chosen
algebraic structure, not D4- or Monster-equivariant by itself.
"""
from __future__ import annotations
from itertools import product
import json
F81=tuple(product(range(3),repeat=4))
POLY=(2,1,0,0,1)
ZERO=(0,0,0,0)
ONE=(1,0,0,0)
ALPHA=(0,1,0,0)

def add(a,b):
    return tuple((x+y)%3 for x,y in zip(a,b))

def mul(a,b):
    p=[0]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            p[i+j]=(p[i+j]+x*y)%3
    for i in range(6,3,-1):
        for j in range(4):
            p[i-4+j]=(p[i-4+j]-p[i]*POLY[j])%3
    return tuple(p[:4])

def power(x,n):
    v=ONE
    while n:
        if n&1:v=mul(v,x)
        x=mul(x,x)
        n>>=1
    return v

def trace(x):
    y=ZERO
    for n in (1,3,9,27):
        y=add(y,power(x,n))
    assert y[1:]==(0,0,0)
    return y[0]

def audit():
    basis=[ONE,ALPHA,power(ALPHA,2),power(ALPHA,3)]
    gram=[[trace(mul(a,b)) for b in basis] for a in basis]
    expected=[[1,0,0,0],[0,0,0,1],[0,0,1,0],[0,1,0,0]]
    assert gram==expected
    # The trace-dual basis is the same permutation because Gram^2=I.
    def dual(b):
        return b[0],b[3],b[2],b[1]
    for a,b in product(F81,repeat=2):
        assert trace(mul(a,dual(b)))==sum(x*y for x,y in zip(a,b))%3
    return {
       "source_quartic":"X^4+X+2 over F3",
       "trace_degree":4,
       "trace_gram":gram,
       "trace_dual_coefficient_rechart":"(b0,b3,b2,b1)",
       "ordered_pair_tests":81*81,
       "all_trace_dot_identifications_pass":True,
       "jfine_two_four_trit_shells_admit_F81_coordinates":True,
       "full_D4_or_global_S3_Heisenberg_automorphism_claimed":False,
       "literal_Monster_representation_intertwiner_claimed":False,
       "agda_kernel_receipt":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
