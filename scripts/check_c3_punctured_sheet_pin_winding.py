#!/usr/bin/env python3
"""Punctured T9 sheet, C3 braid and Pin/O(2) reflection: exact checks.
A geometric puncture is a removed origin, not a Pin-group generator.
"""
from fractions import Fraction as Q
from math import atan2, pi

P=[(-1,1),(0,1),(0,0),(0,-1),(1,-1),(1,0),
   (1,1),(0,1),(0,0),(0,-1),(-1,-1),(-1,0)]
mirror=lambda p:(-p[0],p[1])
punctured={(x,y) for x in (-1,0,1) for y in (-1,0,1) if (x,y)!=(0,0)}
assert len(punctured)==8
assert {mirror(p) for p in punctured}==punctured
assert all(mirror(mirror(p))==p for p in punctured)
# Every one of the three phase-shifted strands encounters the centre.
for j in range(3):
    assert [k for k in range(12) if P[(k+4*j)%12]==(0,0)]==[(2-4*j)%12,(8-4*j)%12] or sorted(k for k in range(12) if P[(k+4*j)%12]==(0,0))==sorted([(2-4*j)%12,(8-4*j)%12])
# A punctured-plane closed loop on the eight surrounding positions:
loop=[(1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1),(1,0)]
def orient(a,b):
    return a[0]*b[1]-a[1]*b[0]
# Every edge is away from origin, with positive oriented angular increments.
def winding(path):
    steps=[]
    for a,b in zip(path,path[1:]):
        assert a!=(0,0) and b!=(0,0)
        cross=orient(a,b);dot=a[0]*b[0]+a[1]*b[1]
        assert not (cross==0 and dot<0), "angular discontinuity: antipodal edge"
        steps.append(atan2(cross,dot))
    return round(sum(steps)/(2*pi))
assert winding(loop)==1
assert winding([mirror(p) for p in loop])==-1
assert winding([mirror(mirror(p)) for p in loop])==1
print("PASS T9 punctured sheet 8 noncentral points, reflection involution")
print("PASS original three-strand braid crosses puncture: no origin-punctured winding lift")
print("PASS perimeter loop winding +1, mirrored winding -1, twice-reflected +1")
print("LIMIT Pin lift requires an independent Clifford/frame lift and a compatible connection")
