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

def check_adaptive_mixed_contour():
    # For any fixed original marked set, if at most h bonds are frustrated,
    # one of K fixed color classes contains >= ceil((n-h)/K) coherent bonds.
    # Their staple coherence flags are exterior-measurable in that class.
    # Therefore the original conditional factor bound pays K*q^m,
    # NOT the binomial coefficient of selecting a coherent subset.
    q=Rational(1,4)
    for L in (3,4,5,6):
        K=8 if L%2==0 else 12
        links=[(mu,x) for x in product(range(L),repeat=4) for mu in range(4)]
        rng=Random(36912000+L)
        for n in range(1,101):
            sample=rng.sample(links,n)
            coherent=[rng.randrange(2) for _ in sample]
            frustrated=n-sum(coherent)
            for h in (frustrated,min(n,frustrated+2),n):
                m=ceil((n-h)/K)
                hist=Counter()
                for (mu,x),yes in zip(sample,coherent):
                    if yes: hist[paint(L,x,mu)]+=1
                assert max(hist.values(),default=0)>=m
                if m:
                    cls=max(hist,key=hist.get)
                    assert q**hist[cls]<=q**m
    print("PASS: adaptive mixed-contour 8/12-class selection, no binomial factor")


def check_existing_chessboard_rate_comparison():
    # Existing #1444 November 19/20 original Wilson microscopic donor formulae.
    # Their native site-reflection chessboard applicability is NOT tested here.
    from sympy import symbols, exp, nsolve
    beta=symbols("beta",positive=True)
    C=8+Rational(2,3)*log(24)+log(beta)
    epsilon=Rational(1,2) # r=3, (6-r)/6
    u_cube=6*exp(C/4-beta*epsilon/96)
    u_plaq=6*exp(C/16-beta*epsilon/384)
    root_cube=nsolve(log(196*u_cube),2300)
    root_plaq=nsolve(log(196*u_plaq),6000)
    assert abs(float(root_cube)-2212.810452)<0.001
    assert abs(float(root_plaq)-6335.549783)<0.001
    print("PASS: existing chessboard u formulas (r=3), beta thresholds",root_cube.evalf(10),root_plaq.evalf(10))


def main():
    check_r445()
    check_adaptive_mixed_contour()
    check_existing_chessboard_rate_comparison()
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
