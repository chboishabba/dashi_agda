#!/usr/bin/env python3
"""H07 exact finite marked affine graph-chart and pivot-overlap audit.
Source chart: graph (u,v,A*u+B*v+b) in F3^5, with A,B,b in F3^3.
No global Grassmannian or real Stiefel equivalence asserted.
"""
from itertools import product

T=(0,1,2)
def evaluate(p,u,v):
    A,V,B=p
    return (u,v,*((B[i]+u*A[i]+v*V[i])%3 for i in range(3)))

def pivot02(p):
    A,V,B=p
    if V[0]==0: return None
    inv=pow(V[0],-1,3)
    a0=(-A[0]*inv)%3
    v0=inv
    b0=(-B[0]*inv)%3
    return ((a0,*((A[i]+V[i]*a0)%3 for i in (1,2))),
            (v0,*((V[i]*inv)%3 for i in (1,2))),
            (b0,*((B[i]+V[i]*b0)%3 for i in (1,2))))

def evaluate02(p,u,w):
    A,V,B=p
    dep=tuple((B[i]+u*A[i]+w*V[i])%3 for i in range(3))
    return (u,dep[0],w,dep[1],dep[2])

planes=set()
overlap=0
for values in product(T,repeat=9):
    p=(values[0:3],values[3:6],values[6:9])
    original=frozenset(evaluate(p,u,v) for u,v in product(T,repeat=2))
    assert len(original)==9
    assert original not in planes
    planes.add(original)
    q=pivot02(p)
    if q is None: continue
    overlap+=1
    assert frozenset(evaluate02(q,u,w) for u,w in product(T,repeat=2))==original

assert len(planes)==19683
assert overlap==13122
assert len(planes)-overlap==6561
print('PASS H07 unique marked source planes 19683, nine points each')
print('PASS pivot01/pivot02 13122 exact overlapping planes; 6561 rejected')
