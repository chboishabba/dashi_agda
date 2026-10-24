#!/usr/bin/env python3
"""SU2 one-plaquette Wilson controls and rotation-error sensitivity.

A,B are perpendicular quaternion spin rotations. This is a real-world
simulator MODEL; not a physical horned-sphere experiment or a proof of
flatness. The one-step Q8 commutator is -I, but only the perfect 2I
target supports the infinite horn recursion (separate scale audit).
"""
from fractions import Fraction as F
from math import cos,radians
def mult(a,b):
 w,x,y,z=a;W,X,Y,Z=b
 return (w*W-x*X-y*Y-z*Z,w*X+x*W+y*Z-z*Y,
         w*Y-x*Z+y*W+z*X,w*Z+x*Y-y*X+z*W)
def inverse(q):
 w,x,y,z=q
 return (w,-x,-y,-z)
def comm(a,b):return mult(mult(mult(a,b),inverse(a)),inverse(b))
ONE=(F(1),F(0),F(0),F(0));NEG=(-F(1),F(0),F(0),F(0))
I=(F(0),F(1),F(0),F(0));J=(F(0),F(0),F(1),F(0))
assert comm(I,J)==NEG and mult(NEG,NEG)==ONE
for ca,sa,cb,sb in [(F(0),F(1),F(0),F(1)),
                      (F(3,5),F(4,5),F(5,13),F(12,13)),
                      (-F(3,5),F(4,5),F(0),F(1))]:
 A=(ca,sa,F(0),F(0));B=(cb,F(0),sb,F(0))
 C=comm(A,B)
 assert C[0]==1-2*sa*sa*sb*sb
 assert 2*C[0]==2-4*sa*sa*sb*sb
 assert sum(x*x for x in C)==1
print("PASS exact SU2/Q8 central -I commutator; trace -2 vs U1 +2")
print("PASS exact Wilson trace: 2-4 sin²(alpha) sin²(beta)")
print("error_degrees,half_trace")
for d in (0,1,5,10,20):
 print(f"{d},{1-2*cos(radians(d))**4:.8f}")
print("NOT evidence of infinite wild embedding, topology-protected response, or physical measurement")
