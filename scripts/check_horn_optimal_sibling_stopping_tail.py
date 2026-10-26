#!/usr/bin/env python3
"""Exact optimized sibling-stop and qualitative tail audit.

Original Hatcher Example 2B.2 owns marked commutator topology;
Agda #1249 / Lean #84 previously owned the universal one-fast
descendant factor-2 criterion. This test CORRECTS our earlier
product-only one-short negative-control wording. It adds the min
of every sibling/leaf stop, including real per-prefix curvature
errors, and a tail mechanism not implied by a single tiny leaf.

No genuine Hatcher metric loops, source homotopy surfaces or
theorem-prover receipt is constructed here.
"""
from fractions import Fraction as F

def amp(x):
    assert F(0)<=x<=2
    return 2*min(F(1),x)

def full(gaps,errs,leaf=F(2)):
    y=leaf
    for g,e in reversed(list(zip(gaps,errs))):
        y=e+amp(g)*y
    return y

def opt(gaps,errs):
    assert len(gaps)==len(errs)
    p=F(1)
    prefix=F(0)
    best=F(2)
    for g,e in zip(gaps,errs):
        assert e>=0
        prefix+=p*e
        # Direct sibling stop via d([A,B])<=2d(B)
        best=min(best,prefix+2*p*g)
        p*=amp(g)
        # Universal selected child stop via d(Uchild)<=2
        best=min(best,prefix+2*p)
    return best

for small in [(0,),(1,),(2,),(0,1),(0,2),(1,2)]:
    g=[F(1,4) if k in small else F(2) for k in range(3)]
    old=full(g,[F(0)]*3)
    new=opt(g,[F(0)]*3)
    assert new<=min(F(2),old)
    if small==(0,): assert old==4 and new==F(1,2)
    if small==(1,): assert old==4 and new==1
    if small==(2,): assert old==4 and new==2
    if len(small)==2: assert new<=1
print('PASS all six 3-level placements; product-only one-short negative control corrected')

# A genuine tail contraction different from any single-fast-descendant:
# each sibling gap exceeds the source universal single-leaf threshold.
gaps=[F(2)]*5+[F(2,5)]*80
first=next(n for n in range(1,len(gaps)+1)
           if opt(gaps[:n],[F(0)]*n)<1)
assert first==21
assert all(gaps[k]>F(1,2**(k+1)) for k in range(len(gaps)))
assert opt(gaps[:first-1],[F(0)]*(first-1))>=1
print('PASS late constant 2/5 sibling tail: depth 21, NO tiny individual descendant')

# Only eventual strict bound c<1/2 is needed, no exponential q^k.
for K,expected in [(0,4),(2,12),(5,24),(8,36)]:
    g=[F(2)]*K+[F(2,5)]*100
    n=next(n for n in range(K+1,len(g)+1)
           if full(g[:n],[F(0)]*n)<=1)
    assert n==expected
    assert full(g[:n-1],[F(0)]*(n-1))>1
print('PASS qualitative eventual contraction with K=0,2,5,8')

# Actual curved prefix only pays defects before the stop.
g=[F(1,4),F(2),F(2)]
assert opt(g,[F(0),F(2),F(2)])==F(1,2)
assert opt(g,[F(2),F(0),F(0)])==2
print('PASS curvature-prefix locality plus fail-closed root defect')
print('OPEN actual Hatcher same-object sibling loop geometry and Stokes homotopies')
