#!/usr/bin/env python3
"""Exact original periodic Z_L^4 Wilson plaquette-conflict coloring (SymPy local).
Proof for all L is in Docs/physics/YMClayOriginalWilsonPeriodicConflictColoring12R44520261121.md.
Not a numerical Wilson probability or Agda/Clay theorem.
"""
from collections import Counter
from itertools import product
from math import ceil
from random import Random
from sympy import Rational, log

def coord_color(L, j):
    assert L >= 3 and 0 <= j < L
    return j % 2 if L % 2 == 0 or j < L-1 else 2

def paint(L, x, mu):
    k = 2 if L % 2 == 0 else 3
    return mu * k + (sum(coord_color(L, x[nu]) for nu in range(4) if nu != mu) % k)

def next_x(L, x, axis):
    y=list(x)
    y[axis]=(y[axis]+1)%L
    return tuple(y)

def plaquettes(L):
    for x in product(range(L),repeat=4):
        for mu in range(4):
            for nu in range(mu+1,4):
                yield ((mu,x),(nu,x),(mu,next_x(L,x,nu)),(nu,next_x(L,x,mu)))

def check_L(L):
    k=2 if L%2==0 else 3
    palette=4*k
    counts=Counter()
    for x in product(range(L), repeat=4):
        for mu in range(4):
            counts[paint(L,x,mu)]+=1
    assert len(counts)==palette and sum(counts.values())==4*L**4
    count=0
    for p in plaquettes(L):
        assert len(set(p))==4
        assert len({paint(L,x,mu) for mu,x in p})==4, (L,p)
        count+=1
    assert count==6*L**4
    # Pigeonhole for independent samples of each marked-cardinality class.
    rng=Random(1369000+L)
    links=[(mu,x) for x in product(range(L),repeat=4) for mu in range(4)]
    for n in sorted({0,1,2,3,7,8,11,12,13,19,20,64,65,min(len(links),500)}):
        sample=rng.sample(links,min(n,len(links)))
        hist=Counter(paint(L,x,mu) for mu,x in sample)
        assert max(hist.values(),default=0)>=ceil(len(sample)/palette)
    return (L,palette,4*L**4,6*L**4,min(counts.values()),max(counts.values()))

def check_r445():
    # Actual native R445 selected side-four starts: 16 side-two points,
    # four directions, phase-0 and phase-1 fine links, total 128.
    L=4
    selected=set()
    for c in product(range(2),repeat=4):
        x=tuple(2*j for j in c)
        for mu in range(4):
            selected.add((mu,x))
            selected.add((mu,next_x(L,x,mu)))
    assert len(selected)==128
    assert Counter(paint(L,x,mu) for mu,x in selected)==Counter({0:32,2:32,4:32,6:32})
    for p in plaquettes(L):
        for mu in range(4):
            assert sum(z in selected for z in p if z[0]==mu)<=1
    print("PASS: n=3 R445 128 selected bonds = 4 orientation conflict-free classes x 32; 896 spectators remain")

def main():
    check_r445()
    for L in range(3,12):
        print("PASS L/colors/links/plaquettes/min/max",check_L(L))
    q=Rational(1,10**6)
    for n in range(1,250):
        assert q**ceil(n/12)<=q**ceil(n/19)
        assert q**ceil(n/8)<=q**ceil(n/12)
    for k in (8,12,19):
        threshold=2*(k*log(196)+log(3))
        print("sufficient beta*r threshold",k,threshold.evalf(12))
    print("PASS: all enumerated original plaquettes are 4-color-distinct; exact rational tail-rate improvement")

if __name__=="__main__":
    main()
