#!/usr/bin/env python3
"""Finite integral Cl(3,1) multiplication: exhaustive 16-blade algebra receipt.
Clifford basis order: time e0 square -1, spatial e1..e3 square +1.
"""
from itertools import product

def bitcount(x): return x.bit_count()
def mul(a,b):
    sign=1
    for j in range(4):
        if (b>>j)&1:
            sign*=(-1)**bitcount(a>>(j+1))
    if (a&b)&1: sign*=-1
    return sign,a^b

def basis_action(e,v): return mul(1<<e,v)

def add_vectors(a,b):
    out={}
    for (sign,mask) in a+b:
        out[mask]=out.get(mask,0)+sign
    return {k:v for k,v in out.items() if v}

def check():
    for a,b,c in product(range(16),repeat=3):
        s,d=mul(a,b); t,e=mul(d,c)
        x,y=mul(b,c);z,f=mul(a,y)
        assert (s*t,e)==(x*z,f),(a,b,c)
    for i,j in product(range(4),repeat=2):
        a,b=mul(1<<i,1<<j)
        c,d=mul(1<<j,1<<i)
        if i==j: assert (a,b)==((-1 if i==0 else 1),0)
        else: assert a==-c and b==d
    # Reflection Pin twisted adjoint: -e1*v*e1, e1^-1=e1
    for i in range(4):
        s,a=mul(2,1<<i)
        t,b=mul(a,2)
        assert b==(1<<i)
        assert -s*t==(-1 if i==1 else 1)
    # spin plane e1e2: R=e1e2 with R^2=-1
    s,r=mul(2,4);t,v=mul(r,r)
    assert (s*t,v)==(-1,0)
    print("PASS 4096 Cl(3,1) basis associativity triples")
    print("PASS Clifford squares and 12 distinct-generator anticommutations")
    print("PASS Pin x-reflection on time and all three spatial generators")
    print("PASS spin bivector (e1 e2)^2 = -1")
if __name__=="__main__":check()
