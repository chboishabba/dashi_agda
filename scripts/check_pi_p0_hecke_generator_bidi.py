#!/usr/bin/env python3
"""Finite original Hecke generator/coset BIDI fixture; NOT executed.
The mathematical proof is in Paper9SignedConeHeckeQCoordinate20261125.md.
No claim of analytic modularity or a native proof from these finite checks.
"""
from math import gcd
P = 41
I = (1,0,0,1)
S = (0,-1,1,0)
T = (1,1,0,1)
INF = P
def mul(a,b):
    x,y,z,w=a
    u,v,r,s=b
    return x*u+y*r,x*v+y*s,z*u+w*r,z*v+w*s
def det(a):
    x,y,z,w=a
    return x*w-y*z
def inv(a):
    assert det(a)==1
    x,y,z,w=a
    return w,-y,-z,x
def rep(k):
    return (P,0,0,1) if k==INF else (1,k,0,P)
def edge(g,k):
    if g==T:
        if k==INF: return INF,(1,P,0,1)
        if k==P-1: return 0,T
        return k+1,I
    if g==S:
        if k==INF: return 0,S
        if k==0: return INF,S
        l=(-pow(k,-1,P))%P
        assert (k*l+1)%P==0
        return l,(k,(-k*l-1)//P,P,-l)
    raise ValueError(g)
def main():
    for g in (S,T):
        destinations=[]
        for k in range(P+1):
            l,b=edge(g,k)
            assert det(rep(k))==P and det(b)==1
            assert mul(rep(k),g)==mul(b,rep(l))
            assert mul(mul(inv(b),rep(k)),g)==rep(l)
            destinations.append(l)
        assert sorted(destinations)==list(range(P+1))
    # Actual self-isogeny matrix and S-corrected k=1 representative.
    assert mul(S,rep(1))==(0,-P,1,1)
    assert gcd(41,1)==1
    print("84 generator edges and inverse reconstructions PASS")
if __name__=="__main__":
    main()
