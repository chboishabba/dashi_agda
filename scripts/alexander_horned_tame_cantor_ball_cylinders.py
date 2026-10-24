#!/usr/bin/env python3
"""Actual nested disjoint Euclidean balls for the C3-symmetric TAME Cantor comparison.

Addresses are binary; the outer C3 permutes three orthogonal satellite charts.
Each prefix interval has length L=1/(3*3^n), centre x in [1/6,1/2],
transverse y=1/2, and the 3D cylinder BALL radius 3L/5.
This is a genuine positive-margin nested Euclidean ball system,
not a symbolic 'clopen ball' status or Alexander wild embedding.
"""
from fractions import Fraction as F
from itertools import product

def interval(bits):
    L0=F(1,3)
    low=F(1,6)+L0*sum(
        (F(2*b,3**(j+1)) for j,b in enumerate(bits)),F(0))
    return low,L0/3**len(bits)

def ball(bits):
    low,L=interval(bits)
    return (low+L/2,F(1,2),F(0)),F(3,5)*L

root,r0=ball(())
assert root==(F(1,3),F(1,2),F(0)) and r0==F(1,5)
# Every point of root ball has squared norm bounded by:
# (8/15)^2+(7/10)^2+(1/5)^2 <1.
assert (root[0]+r0)**2+(root[1]+r0)**2+r0*r0<1
# Radial x>0 avoids inward spoke end x=-1/2, while y>1/4
# avoids the two local linked circles with |y|<=1/4.
assert root[0]-r0==F(2,15)>0
assert root[1]-r0==F(3,10)>F(1,4)

count=0
for depth in range(9):
    for bits in product((0,1),repeat=depth):
        c,r=ball(bits)
        assert r==F(1,5*3**depth)
        assert root[0]-r0<=c[0]-r and c[0]+r<=root[0]+r0
        left,rl=ball(bits+(0,));right,rr=ball(bits+(1,))
        assert rl==rr==r/3
        assert abs(left[0]-c[0])+rl<r
        assert abs(right[0]-c[0])+rr<r
        assert right[0]-left[0]-(rl+rr)==F(4,15)*F(1,3**(depth+1))>0
        count+=1
assert count==511
rotate=lambda x:(x[2],x[0],x[1])
satellites=((9,0,0),(0,9,0),(0,0,9))
assert tuple(rotate(x) for x in satellites)==satellites[1:]+satellites[:1]
print("PASS 511 nested clopen cylinders with explicit positive Euclidean separation")
print("PASS genuine ball containment inside each satellite, disjoint from collars and linked loops")
print("PASS exact exterior C3 permutation of three tame Cantor end systems")
print("NOT CERTIFIED: Hatcher wild 3-ball, its exterior fundamental group or Dirac spectrum")
