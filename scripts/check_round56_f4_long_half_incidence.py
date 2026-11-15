#!/usr/bin/env python3
"""Positive B4 equivariant incidence decomposition of the 96 rank-two Round56 cells.

F4 long roots: 24 vectors with two entries +/-2, the rest 0 (doubled roots).
F4 half-roots: 16 full sign vectors +/-1 (doubled roots).
Image is a 96-element compatible subset of long24 x half16: half-root signs
on the support of the long root must coincide. Both projections are B4-equivariant.
No identification with E6-folded W(F4), Albert action, or physical integrand.
"""
from itertools import product

def cells():
    return {v for v in product((-2,-1,1,2),repeat=4) if sum(abs(x)==2 for x in v)==2}

def long(v):
    return tuple(2 if x==2 else -2 if x==-2 else 0 for x in v)

def half(v):
    return tuple(1 if x>0 else -1 for x in v)

def valid(l,h):
    return sum(x!=0 for x in l)==2 and all(x==0 or x//2==s for x,s in zip(l,h))

def decode(l,h):
    assert valid(l,h)
    return tuple(x if x else s for x,s in zip(l,h))

def flip(v,i):
    v=list(v);v[i]=-v[i];return tuple(v)

def swap(v,i):
    v=list(v);v[i],v[i+1]=v[i+1],v[i];return tuple(v)

def run():
    src=cells(); assert len(src)==96
    longs={long(c) for c in src}; halves={half(c) for c in src}
    assert len(longs)==24 and len(halves)==16
    assert all(sum(x*x for x in l)==8 for l in longs)
    assert all(sum(x*x for x in h)==4 for h in halves)
    inc={(l,h) for l in longs for h in halves if valid(l,h)}
    pairs={(long(c),half(c)) for c in src}
    assert pairs==inc and len(pairs)==96
    assert all(decode(long(c),half(c))==c for c in src)
    assert all((long(decode(l,h)),half(decode(l,h)))==(l,h) for l,h in inc)
    assert all(sum(long(c)==l for c in src)==4 for l in longs)
    assert all(sum(half(c)==h for c in src)==6 for h in halves)
    gs=[*(lambda v,i=i:flip(v,i) for i in range(4)),
        *(lambda v,i=i:swap(v,i) for i in range(3))]
    for g in gs:
        assert {g(c) for c in src}==src
        assert {g(l) for l in longs}==longs
        assert {g(h) for h in halves}==halves
        for c in src:
            assert (long(g(c)),half(g(c)))==(g(long(c)),g(half(c)))
        assert {(g(l),g(h)) for l,h in inc}==inc
    print('PASS: 96 rank-two cells biject with 96 compatible (F4 long-root, F4 half-root) incidence pairs')
    print('F4 long roots:',len(longs),'half roots:',len(halves),'constant fibres: 4 and 6')
    print('PASS: 7 source B4 generators commute with both independent coordinate root actions')
    print('LIMIT: not an equivariant bijection onto two *disjoint* F4 root copies or a W(F4) folded-action identification')

if __name__=='__main__':run()
