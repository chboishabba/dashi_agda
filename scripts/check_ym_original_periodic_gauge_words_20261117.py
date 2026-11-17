#!/usr/bin/env python3
"""Exact free-group original periodic 4D six-plane gauge covariance.
Checks BOTH orientations of each positive plaquette at L=1,2,3,4.
No matrices, floating point or assumed Haar law. This accompanies the
universal existing Agda original source theorem:
BalabanClayGate4RationalSU2BondCarrierExact.rationalSU2PlaquetteGaugeCancellation.
Free-group test is a finite regression, not a universal kernel proof.
Attribution: Wilson/Balaban and original DASHI periodic SU2 owners.
"""
from itertools import combinations,product
checks=0
def inv(w):return tuple((a,-s) for a,s in reversed(w))
def multiply(*words):
    stack=[]
    for word in words:
        for label,sign in word:
            if stack and stack[-1]==(label,-sign):stack.pop()
            else:stack.append((label,sign))
    return tuple(stack)
def atom(label):return ((label,1),)
def shift(x,a,sign,L):
    z=list(x);z[a]=(z[a]+sign)%L
    return tuple(z)
def bond(x,a,s,L):
    return atom(('U',x,a)) if s==1 else inv(atom(('U',shift(x,a,-1,L),a)))
def gauged_bond(x,a,s,L):
    end=shift(x,a,s,L)
    return multiply(atom(('G',x)),bond(x,a,s,L),inv(atom(('G',end))))
def path_word(x,steps,L,gauged=False):
    value=();site=x
    for a,s in steps:
        value=multiply(value,
            (gauged_bond if gauged else bond)(site,a,s,L))
        site=shift(site,a,s,L)
    return value,site
def eq(a,b):
    global checks
    assert a==b,(a,b)
    checks+=1
for L in (1,2,3,4):
    cases=0
    for site in product(range(L),repeat=4):
        for a,b in combinations(range(4),2):
            positive=((a,1),(b,1),(a,-1),(b,-1))
            negative=tuple((u,-sgn) for u,sgn in reversed(positive))
            for directions in (positive,negative):
                raw,end=path_word(site,directions,L)
                gauged,endg=path_word(site,directions,L,True)
                eq(end,site)
                eq(endg,site)
                eq(gauged,multiply(atom(('G',site)),raw,inv(atom(('G',site)))))
                cases+=1
            raw,_=path_word(site,positive,L)
            back,_=path_word(site,negative,L)
            eq(back,inv(raw))
            end=shift(site,a,1,L)
            eq(gauged_bond(site,a,1,L),
               multiply(atom(('G',site)),atom(('U',site,a)),inv(atom(('G',end)))))
    print(f"L={L}: plaquettes={6*L**4}; oriented gauge-conjugacy cases={cases}")
print(f"ORIGINAL_PERIODIC_WILSON_GAUGE_WORD_PASS={checks}")
