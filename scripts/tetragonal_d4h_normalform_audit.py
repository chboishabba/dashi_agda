#!/usr/bin/env python3
"""Exact exhaustive independent normal-form ↔ 3x3 matrix audit for D4h.

Classical mathematical result, independently implemented finite certificate.
Does not claim Lean/Agda kernel verification or specimen identity.
"""
from itertools import product

def matmul(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))
I=((1,0,0),(0,1,0),(0,0,1))
R=((0,-1,0),(1,0,0),(0,0,1))
S=((1,0,0),(0,-1,0),(0,0,1))
H=((1,0,0),(0,1,0),(0,0,-1))
def power(a,n):
    z=I
    for _ in range(n): z=matmul(z,a)
    return z
G=list(product(range(4), range(2), range(2)))
def mul(g,h):
    a,b,c=g; d,e,f=h
    return ((a+((-d)%4 if b else d))%4,b^e,c^f)
def matrix(g):
    a,b,c=g
    return matmul(matmul(power(R,a),power(S,b)),power(H,c))
def act(m,p):
    return tuple(sum(m[i][j]*p[j] for j in range(3)) for i in range(3))
def sites():
    return [(x,y,z) for x,y in ((1,0),(0,1),(-1,0),(0,-1)) for z in (-1,1)]
def check():
    e=(0,0,0)
    assert len(G)==16 and len(set(G))==16
    assert len({matrix(g) for g in G})==16
    assert all(mul(e,g)==g==mul(g,e) for g in G)
    assert all(mul(g,( (-g[0] if not g[1] else g[0])%4, g[1],g[2]))==e for g in G)
    assert all(mul(mul(g,h),k)==mul(g,mul(h,k)) for g,h,k in product(G,repeat=3))
    assert all(matrix(mul(g,h))==matmul(matrix(g),matrix(h)) for g,h in product(G,repeat=2))
    xs=sites()
    assert all(act(matrix(g),p) in xs for g in G for p in xs)
    assert len({tuple(act(matrix(g),p) for p in xs) for g in G})==16
    for g,h,p in product(G,G,xs):
        assert act(matrix(mul(g,h)),p)==act(matrix(g),act(matrix(h),p))
    print("PASS: 16 elements, inverse/associativity, faithful matrix/site actions, 256 multiplication pairs, 4096 triples.")
if __name__=="__main__":
    check()
