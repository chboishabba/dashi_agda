#!/usr/bin/env python3
"""Sharp universal two-source Wilson affine zero-free bidisk (exact regression).

For positive original conditional Wilson/Haar laws and REAL marks |F|,|G|<=1,
K(s,t)=K0 E[(1+sF)(1+tG)] != 0 on |s|,|t|<1.
Each segment [1-s,1+s] has sector width <pi/2 since
Re((1+s)conj(1-s))=1-|s|^2>0. Product sectors have width <pi,
and a positive weighted sum cannot be zero. For deficits in [0,2],
the sharp universal radius is 1/2 by rescaling.
This tests exact rational finite instances, NOT original continuous Haar,
renormalized CMP119 T, W3 clustering or OS mass gap.
"""
from fractions import Fraction as Q
from itertools import product

def add(x,y): return (x[0]+y[0],x[1]+y[1])
def scale(c,x): return (c*x[0],c*x[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def norm2(x): return x[0]*x[0]+x[1]*x[1]
ZERO=(Q(0),Q(0))
ONE=(Q(1),Q(0))

def partition(weights,pairs,s,t):
    acc=ZERO
    for w,(f,g) in zip(weights,pairs):
        acc=add(acc,scale(w,mul(add(ONE,scale(f,s)),add(ONE,scale(g,t)))))
    return acc

def main():
    points=[(Q(a,4),Q(b,4)) for a,b in product(range(-3,4),repeat=2)
            if a*a+b*b<16]
    for s in points:
        left=add(ONE,s);right=add(ONE,scale(-1,s))
        dot=left[0]*right[0]+left[1]*right[1]
        assert dot==1-norm2(s)>0

    corners=tuple(product((Q(-1),Q(1)),repeat=2))
    laws=[w for w in product(range(4),repeat=4) if sum(w)]
    assert len(laws)==255 and len(points)==45
    checks=0
    for w in laws:
        for s in points:
            for t in points:
                assert partition(w,corners,s,t)!=ZERO
                checks+=1
    assert checks==516375

    # Sharp universal open radius, reached by an atom at the boundary.
    assert partition((1,),((Q(1),Q(1)),),(Q(-1),Q(0)),ZERO)==ZERO
    assert partition((1,),((Q(2),Q(0)),),(Q(-1,2),Q(0)),ZERO)==ZERO

    # Same 1/F/G/FG provenance; source analyticity does not force spatial decay.
    correlated=partition((1,1),((Q(1),Q(1)),(Q(-1),Q(-1))),ZERO,ZERO)
    assert correlated==(Q(2),Q(0))
    print(f"PASS {checks} exact positive original two-mark source evaluations")
    print("PASS sharp bidisk |s|,|t|<1 normalized marks; <1/2 deficits")
    print("PASS boundary zeros and no spatial-clustering promotion")
    print("OPEN physical CMP119, absolute W3 and interacting OS mass gap")

if __name__=="__main__":
    main()
