#!/usr/bin/env python3
"""Exact Round56 240 ↔ (15 nonempty outer supports × 16 F4 half-root signs).

Checks the original 4 signed intervals, 7 W(B4) generators, and F3
linearisation ranks. The support/sign PAIR is lossless; separately
aggregating each marginal is not. This is not a folded F4/E6/E8 action.
"""
from itertools import product
from collections import Counter

cells = tuple(c for c in product((-2,-1,1,2),repeat=4) if any(abs(x)==2 for x in c))
support = lambda c: tuple(abs(x)==2 for x in c)
half = lambda c: tuple(x>0 for x in c)

def reconstruct(m,h):
    return tuple((2 if o else 1)*(1 if s else -1) for o,s in zip(m,h))

def action(c,g):
    op,i=g
    a=list(c)
    if op=="flip":a[i]=-a[i]
    else:a[i],a[i+1]=a[i+1],a[i]
    return tuple(a)

generators=tuple(("flip",i) for i in range(4))+tuple(("swap",i) for i in range(3))

def mask_action(m,g):
    return m if g[0]=="flip" else action(m,g)

def half_action(h,g):
    if g[0]=="swap":return action(h,g)
    a=list(h);a[g[1]]=not a[g[1]]
    return tuple(a)

def gf3_rank(rows):
    a=[list(map(lambda v:v%3,row)) for row in rows]
    r=0
    for col in range(len(a[0])):
        k=next((i for i in range(r,len(a)) if a[i][col]),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r]
        if a[r][col]==2:a[r]=[(2*v)%3 for v in a[r]]
        for k in range(len(a)):
            if k!=r and a[k][col]:
                t=a[k][col]
                a[k]=[(v-t*w)%3 for v,w in zip(a[k],a[r])]
        r+=1
        if r==len(a):break
    return r

def test():
    masks=sorted({support(c) for c in cells})
    halves=sorted({half(c) for c in cells})
    assert (len(cells),len(masks),len(halves))==(240,15,16)
    assert {(support(c),half(c)) for c in cells}==set(product(masks,halves))
    assert all(reconstruct(support(c),half(c))==c for c in cells)
    assert all((support(reconstruct(m,h)),half(reconstruct(m,h)))==(m,h)
               for m,h in product(masks,halves))
    assert Counter(sum(support(c)) for c in cells)=={1:64,2:96,3:64,4:16}
    for g in generators:
        assert {action(c,g) for c in cells}==set(cells)
        assert all((support(action(c,g)),half(action(c,g)))==
                   (mask_action(support(c),g),half_action(half(c),g))
                   for c in cells)
    p=[[int(support(c)==m) for c in cells] for m in masks]
    q=[[int(half(c)==h) for c in cells] for h in halves]
    assert (gf3_rank(p),gf3_rank(q),gf3_rank(p+q))==(15,16,30)
    assert all(sum(row)==16 for row in p)
    assert all(sum(row)==15 for row in q)
    print("PASS: 240=(15 nonempty support masks)×(16 F4 half-root signs)")
    print("PASS: all 7 W(B4) generators, inverse encoding, 64+96+64+16")
    print("PASS: GF3 marginal ranks 15,16, combined rank30, kernel210")
    print("OPEN: folded E6/F4 identification, full E8, physical integrand")

if __name__=="__main__":test()
