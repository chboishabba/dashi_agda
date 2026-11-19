#!/usr/bin/env python3
"""Original configured side-four Green; exact raw Wilson AAqq and Haar contractions.
The original Agda mixed vertex is the polarized diagonal derivative (check its
factorial conventions separately). Here vertices are full labelled derivatives.
No claim of CMP109 physical beta or constrained continuum normalization.
"""
from fractions import Fraction as F
from collections import defaultdict
from check_ym_p33_fourier_vertices_20261119 import (
    SITES, PLANES, phase, terms, slot_coords, add, mul, scale, ZERO, ONE)
from functools import lru_cache
N=len(SITES); O=(0,0,0,0)
def neg(p):return tuple(-v%4 for v in p)
def diff(x,y):return tuple((a-b)%4 for a,b in zip(x,y))
def weight(p):return F(1, sum((0,2,4,2)[v] for v in p) or 1)
@lru_cache(None)
def green(x):
    z=tuple(sum(weight(p)*phase(p,x)[i] for p in SITES)/N for i in range(2))
    assert z[1]==0
    return z[0]
def local_contraction(left,right):
    # Collapse the original coordinate basis sums using the component-diagonal
    # G_ab. For each plaquette and internal color/axis, the two slot positions
    # are precisely the coordinate rows/columns. External waves are unnormalized.
    result=ZERO
    for mu,nu in PLANES:
        slots=slot_coords(O,mu,nu)
        for axis in (mu,nu):
            for color in (1,2,3):
                legs=(left,right,(axis,color,O),(axis,color,O))
                for where,c in terms(legs,mu,nu):
                    x,y=(slots[where[j]][0] for j in (2,3))
                    z=mul(phase(left[2],slots[where[0]][0]),phase(right[2],slots[where[1]][0]))
                    result=add(result,scale(z,c*green(diff(x,y))))
    # Translation sum of external pair is N or zero.
    return scale(result,F(N,24) if right[2]==neg(left[2]) else 0)
def momentum_contraction(left,right):
    # The same original Green spectral sum, inserted in both internal slots.
    # Cache local allocation data, but independently evaluate every momentum.
    result=ZERO
    if right[2]!=neg(left[2]):return result
    for mu,nu in PLANES:
        slots=slot_coords(O,mu,nu)
        for axis in (mu,nu):
            for color in (1,2,3):
                legs=(left,right,(axis,color,O),(axis,color,O))
                for where,c in terms(legs,mu,nu):
                    z=mul(phase(left[2],slots[where[0]][0]),phase(right[2],slots[where[1]][0]))
                    for p in SITES:
                        w=mul(phase(p,slots[where[2]][0]),phase(neg(p),slots[where[3]][0]))
                        result=add(result,scale(mul(z,w),F(c,24)*weight(p)))
    return result
def main():
    assert sum(green(x) for x in SITES)==1
    for x in SITES:
        lap=8*green(x)
        for j in range(4):
            for s in (-1,1):
                y=tuple((v+s*(i==j))%4 for i,v in enumerate(x));lap-=green(y)
        assert lap+F(1,N)==int(x==O)
    print('PASS all 256 original configured Green inverse equations and normalization')
    for axis,p in [(0,O),(1,(1,0,0,0)),(0,(1,0,0,0)),(1,(1,1,0,0)),(2,(2,1,0,1))]:
        left=(axis,1,p);right=(axis,1,neg(p))
        a=local_contraction(left,right);b=momentum_contraction(left,right)
        assert a==b,(left,a,b)
        print('AAqq',axis,p,a)
    haar=F(1,3)*12*N*green(O)
    assert haar==4*sum(weight(p) for p in SITES)
    print('Haar raw (1/3) Tr G =',haar)
    print('OPEN bubble, reduced FP, background symmetry factors, Ward and beta')
if __name__=='__main__':main()
