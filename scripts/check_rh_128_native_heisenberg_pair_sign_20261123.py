#!/usr/bin/env python3
"""Native Monster3BFiniteHeisenbergCentralExtensionExact: paired six-sign action.

Checks standard F3^6 translation/dual/center H6 cocycle, symplectic J,
all 64 signed six-coordinate masks, 4096 pairwise compositions, 19200
seeded exact finite group tests, and a primal-only non-automorphism.
An actual normalizer element in Monster is NOT identified.
"""
from itertools import product
from random import Random
import sympy as s

I=s.eye(6); O=s.zeros(6)
J=O.row_join(I).col_join((-I).row_join(O))
masklist=list(product((0,1),repeat=6))
assert len(masklist)==64
for m in masklist:
    D=s.diag(*[1-2*x for x in m])
    S=D.row_join(O).col_join(O.row_join(D))
    assert S.T*J*S==J and S*S==s.eye(12)
    unpaired=D.row_join(O).col_join(O.row_join(I))
    if any(m): assert unpaired.T*J*unpaired!=J
    for n in masklist:
        E=s.diag(*[1-2*x for x in n])
        N=E.row_join(O).col_join(O.row_join(E))
        combined=s.diag(*[1-2*(x^y) for x,y in zip(m,n)])
        T=combined.row_join(O).col_join(O.row_join(combined))
        assert S*N==N*S==T
print('PASS native 64 six-axis paired symplectic matrices, 4096 compositional pairs')

rng=Random(369)
def add(x,y):return tuple((a+b)%3 for a,b in zip(x,y))
def dot(x,y):return sum(a*b for a,b in zip(x,y))%3
def compose(g,h):
    x,xi,c=g;y,eta,d=h
    return add(x,y),add(xi,eta),(c+d+dot(xi,y))%3
def act(mask,g):
    x,xi,c=g
    factors=tuple((-1 if bit else 1) for bit in mask)
    return (tuple(a*e%3 for a,e in zip(x,factors)),
            tuple(a*e%3 for a,e in zip(xi,factors)),c)
for mask in masklist:
    for _ in range(300):
        g=(tuple(rng.randrange(3) for _ in range(6)),
           tuple(rng.randrange(3) for _ in range(6)),rng.randrange(3))
        h=(tuple(rng.randrange(3) for _ in range(6)),
           tuple(rng.randrange(3) for _ in range(6)),rng.randrange(3))
        assert act(mask,compose(g,h))==compose(act(mask,g),act(mask,h))
        x,xi,_=g;y,eta,_=h
        fx,fxi,_=act(mask,g);fy,feta,_=act(mask,h)
        assert (dot(x,eta)-dot(y,xi))%3==(dot(fx,feta)-dot(fy,fxi))%3
print('PASS 19200 native Heisenberg cocycle+symplectic invariance tests')

def primal_only(g):
    x,xi,c=g
    return ((-x[0])%3,)+x[1:],xi,c
g=((0,)*6,(1,0,0,0,0,0),0)
h=((1,0,0,0,0,0),(0,)*6,0)
assert primal_only(compose(g,h))!=compose(primal_only(g),primal_only(h))
print('PASS primal-only sign flip fails central cocycle; paired dual required')
print('OPEN actual Monster normalizer and RH selected-W zero-side group action')
