#!/usr/bin/env python3
"""Exact integer audit of the D4h ⋉ Z^3 primitive tetragonal Seitz model.

Matches TetragonalPrimitiveSeitzExact.agda operation conventions.
Covers all 16 linear parts and a nontrivial finite translation fixture.
Tests mathematical semantics; not an Agda compiler or specimen receipt.
Classical source: IUCr / crystallographic Seitz affine conventions.
"""
from itertools import product

G=list(product(range(4),(False,True),(False,True)))
zero=(0,0,0)
e=(0,False,False)

def neg(x): return tuple(-a for a in x)
def plus(x,y):return tuple(a+b for a,b in zip(x,y))
def linear(g,p):
    q,b,c=g
    x,y,z=p
    if c:z=-z
    if b:y=-y
    for _ in range(q): x,y=-y,x
    return x,y,z
def compose(g,h):
    a,b,c=g;d,u,v=h
    return ((a+(-d if b else d))%4,b^u,c^v)
def inverse(g):
    a,b,c=g
    return ((-a)%4 if not b else a,b,c)
def multiply(s,t):
    g,x=s;h,y=t
    return compose(g,h),plus(x,linear(g,y))
def invert(s):
    g,t=s
    h=inverse(g)
    return h,linear(h,neg(t))
def act(s,p):
    g,t=s
    return plus(t,linear(g,p))
unit=(e,zero)
basis=[zero,(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
assert len({tuple(linear(g,p) for p in basis) for g in G})==16
for g in G:
    assert compose(g,inverse(g))==e
    assert compose(inverse(g),g)==e
    for p in product(range(-2,3),repeat=3):
        assert linear(e,p)==p
        assert linear(inverse(g),linear(g,p))==p
        assert linear(g,neg(p))==neg(linear(g,p))
for g,h in product(G,repeat=2):
    for p in product((-1,0,1),repeat=3):
        assert linear(compose(g,h),p)==linear(g,linear(h,p))
for g,h,k in product(G,repeat=3):
    assert compose(compose(g,h),k)==compose(g,compose(h,k))
for g,t in product(G,basis):
    s=(g,t)
    assert multiply(unit,s)==s
    assert multiply(s,unit)==s
    assert multiply(invert(s),s)==unit
    assert multiply(s,invert(s))==unit
# Nontrivial checks of affine composition/associativity with integer shifts.
for g,h in product(G,repeat=2):
    for x,y,p in product(basis[:4],basis[:4],basis):
        s=(g,x);t=(h,y)
        assert act(multiply(s,t),p)==act(s,act(t,p))
for g,h,k in product(G,repeat=3):
    s=(g,(1,0,0));t=(h,(0,-1,0));u=(k,(0,0,1))
    assert multiply(multiply(s,t),u)==multiply(s,multiply(t,u))
print("PASS: 16 D4h group elements and affine Z3 Seitz unit/inverse laws")
print("PASS: 256x translations affine action and all 4096 Seitz associativity triples")
