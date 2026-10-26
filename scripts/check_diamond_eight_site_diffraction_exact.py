#!/usr/bin/env python3
"""Exact diamond ideal-basis diffraction and reciprocal parity regression.

Prior art: IUCr Fd-3m #227, International Tables; IUCr reflection
conditions; classical diamond structure factor.
This is deterministic math, not a measured sample or sensor signal.
Co-ordinate convention: positions measured in conventional-cell quarters.
"""
from collections import Counter
from itertools import product

ROOT=((1,0),(0,1),(-1,0),(0,-1))
FCC=((0,0,0),(0,2,2),(2,0,2),(2,2,0))
DELTA=(1,1,1)
B=tuple(tuple((x+y)%4 for x,y in zip(r,DELTA)) for r in FCC)
MOTIF=FCC+B
assert len(set(MOTIF))==8

def add(x,y):return (x[0]+y[0],x[1]+y[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def norm2(x):return x[0]**2+x[1]**2
def phase(hkl,r):return ROOT[sum(x*y for x,y in zip(hkl,r))%4]
def summation(items):
    out=(0,0)
    for v in items:out=add(out,v)
    return out
def amp(hkl,positions):return summation(phase(hkl,r) for r in positions)
def centring_allowed(hkl):
    return all(sum(a*b for a,b in zip(hkl,t))%4==0 for t in FCC[1:])

counts=Counter()
for hkl in product(range(4),repeat=3):
    h,k,l=hkl
    actual=amp(hkl,MOTIF)
    factor=mul(amp(hkl,FCC),add((1,0),phase(hkl,DELTA)))
    assert actual==factor,(hkl,actual,factor)
    reciprocal=all(x%2==h%2 for x in hkl)
    assert centring_allowed(hkl)==reciprocal
    predicted=(0 if not reciprocal or (h+k+l)%4==2 else
               64 if (h+k+l)%4==0 else 32)
    assert norm2(actual)==predicted,(hkl,actual,predicted)
    counts[predicted]+=1
assert counts==Counter({0:52,32:8,64:4}),counts

assert norm2(amp((1,1,1),MOTIF))==32
assert norm2(amp((2,2,2),MOTIF))==0
assert norm2(amp((4,0,0),MOTIF))==64
assert centring_allowed((2,2,2))

# Uniform two-sublattice contrast: a=(1,0), b=(0,0).
# This is NOT a single isolated NV vacancy model.
a_only_222=amp((2,2,2),FCC)
assert norm2(a_only_222)==16

# Explicitly link the eight positions to the primitive FCC basis
# used by DiamondFccPrimitiveGlideExact.
def primitive(u,v,w):return (2*(v+w),2*(u+w),2*(u+v))
fcc_from_primitive={tuple(t%4 for t in primitive(u,v,w))
                    for u,v,w in product((0,1),repeat=3)}
assert fcc_from_primitive==set(FCC)
assert set(MOTIF)==fcc_from_primitive | {
    tuple((a+b)%4 for a,b in zip(x,DELTA)) for x in fcc_from_primitive}

print("PASS: 8 source-model sites and exact phase factorisation in Z[i]")
print("PASS: 64 reciprocal residue classes, fcc parity iff primitive pairing")
print("PASS: ideal diamond relative intensities: zero=52, 32=8, 64=4")
print("PASS: motif-specific 222 extinction; uniform contrast restores 222")
