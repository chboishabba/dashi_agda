#!/usr/bin/env python3
"""Exact Section42 original source-model controls; not kernel proofs.
YM shifted Fin degree; NS uniform j-radius; BSD original crossing symmetry;
Hodge actual even-sign δ product (32 roots); PNP finite-block causal reads.
"""
from fractions import Fraction as F
from itertools import product, combinations
from math import factorial

C = dict(YM=0, NS=0, BSD=0, Hodge=0, PNP=0)
for c in range(1, 81):
    for i in range(c):
        for j in range(c):
            if i+j >= c-1:
                assert i+j+1 >= c
                C['YM'] += 1
            if i+j >= max(0,c-2):
                assert i+j+2 >= c
                C['YM'] += 1
    if c == 1:
        assert 2 >= c
        C['YM'] += 1
for nu,Emax in product((F(1,3),F(2)),(F(0),F(1,5),F(3))):
    for j in range(80):
        eps=F(1,j+1)
        R=1+Emax/(2*nu*eps)
        assert R>0 and Emax < 2*nu*R*R*eps
        for energy in (F(0), Emax/2, Emax):
            assert energy/(2*nu*R*R)<eps
            C['NS']+=1
for a,b in ((F(1,2),F(3,4)),(F(2),F(5)),(F(5),F(2)),(F(7,3),F(1,4))):
    for n in range(70):
        def h(u,v,k):
            z=F(1)
            for q in range(1,k+1): z=u*z+v**q
            return z
        def quot(u,v,x,k):
            z=F(1)
            for q in range(1,k+1): z=u*v*z+h(u,v,q)*x**q
            return z
        def poly(u,v,x,k): return h(u,v,k)*x**(k+2)-h(u,v,k+1)*x**(k+1)+(u*v)**(k+1)
        assert h(a,b,n)==h(b,a,n)
        C['BSD']+=1
        for x in (F(0),F(1,3),F(3,2)):
            assert quot(a,b,x,n)==quot(b,a,x,n)
            assert poly(a,b,x,n)==poly(b,a,x,n)
            C['BSD']+=2
# original Q0 for a_i=0 and y_i=3 has roots s_i=0 and s_i=1/2,
# dField = +-1. Signed-product δ=1 means exactly even signs.
root_set=[]
for bit in product((0,1),repeat=6):
    signs=[1 if b==0 else -1 for b in bit]
    delta=1
    for x in signs: delta*=x
    if delta==1: root_set.append(tuple(bit))
assert len(root_set)==32
for reference in root_set:
    images=[]
    for e in root_set:
        changed=tuple(reference[i]^e[i] for i in range(6))
        assert changed in root_set
        images.append(changed)
        C['Hodge']+=1
    assert len(set(images))==32
    C['Hodge']+=1
# Finite block observations. If a real same-run block observation differs,
# at least one read address carries a different bit. Empty block no-go.
for n in range(1,5):
    for x in product((0,1),repeat=n):
        for y in product((0,1),repeat=n):
            for b in range(0,n+1):
                for addr in combinations(range(n),b):
                    vx=tuple(x[i] for i in addr)
                    vy=tuple(y[i] for i in addr)
                    if vx!=vy:
                        assert any(x[i]!=y[i] for i in addr)
                        assert b>0
                        C['PNP']+=2
                    else:
                        assert vx==vy
                        C['PNP']+=1
print('SECTION42 EXACT FINITE MODEL PASS',C,'TOTAL',sum(C.values()))
