#!/usr/bin/env python3
"""R445 original 64 ordered coarse links -> signed P3^9 TWO-STEP path,
with source odd-site 1/3 residual needed for local SU2 gauge covariance.

Original owner YMClayNativeSideFourTwoLinkPairSameObjectExact:
actual fine SU(N) blocked holonomy equals ordered U_first U_second.
This is exact Q8 subset of SU2 finite model, no full Wilson measure/Haar.
"""
from itertools import product
from collections import defaultdict
import sympy as S
I=S.eye(2);A=S.Matrix([[0,1],[-1,0]]);B=S.diag(S.I,-S.I)
assert A.det()==B.det()==1 and A.H*A==B.H*B==I
assert A*B!=B*A
site2=tuple(product((0,1),repeat=4))
def tritfine(p):
    return tuple(0 if v%2 else (1 if v==2 else -1) for v in p)+(0,)*5
def first(c,d):
    x=[2*a for a in c];return tuple(x)
def nextfine(p,d):
    x=list(p);x[d]=(x[d]+1)%4;return tuple(x)
def gauge(p):
    odd=[x for x in p if x%2]
    if not odd:return I
    assert len(odd)==1
    return A if odd[0]==1 else B
def finefield(p,d):return A if p[d]%2==0 else B
middle=defaultdict(set);raw=set();signed=set();lifted=set()
for c in site2:
    for d in range(4):
        a=first(c,d);b=nextfine(a,d);z=nextfine(b,d)
        x,m,y=tritfine(a),tritfine(b),tritfine(z)
        assert tritfine(a)==tuple(2*v-1 for v in c)+(0,)*5
        assert all(sum(i!=j for i,j in zip(p,q))==1
                   for p,q in ((x,m),(m,y)))
        middle[m].add(b)
        U0,U1=finefield(a,d),finefield(b,d)
        assert U0*U1!=U1*U0
        assert (gauge(a)*U0*gauge(b).inv())*(
            gauge(b)*U1*gauge(z).inv())==gauge(a)*U0*U1*gauge(z).inv()
        raw.update(((a,d),(b,d)))
        signed.update(((x,m),(m,y)))
        lifted.update((((x,a),(m,b)),((m,b),(y,z))))
assert len(raw)==len(signed)==len(lifted)==128
assert len(middle)==32
assert all(len(values)==2 for values in middle.values())
assert all(gauge(min(values))!=gauge(max(values)) for values in middle.values())
print("PASS original 16 sites -> 64 coarse bonds -> 128 unique selected source fine bonds")
print("PASS 32 projected midpoints but 64 source odd sites: 32 two-valued residual fibres")
print("PASS noncommutative SU2/Q8 link multiplication and gauge covariance all 64")
print("PASS sign-only midpoint gauge non-factorization on 32 actual collisions")
print("OPEN physical hyperfabric gauge Laplacian and 1024-link Haar/Wilson disintegration")
