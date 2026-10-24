#!/usr/bin/env python3
"""Exact rational C3-equivariant four-ball / three-handle star scaffold.

Classical 3-manifold fact used conditionally:
Boundary-connect four topological 3-balls with three disjoint tame
1-handles attached along collared disks following a TREE; the result
is again a topological B3 (regular neighbourhood of a finite tree).

This file checks finite *geometry and combinatorics*, not the wild
satellite B3 embedding, its tame attachment collars, the thick
handle's isotopy class or the exterior's van Kampen isomorphism.

Reuses DASHI:
  AlexanderHornedC3SatellitePlacementExact
  AlexanderHornedC3OrbitSolidExact
  AlexanderHornedC3ComplementActionExact
"""
from fractions import Fraction as Q

centre=(0,0,0)
satellites=((9,0,0),(0,9,0),(0,0,9))
eps=Q(1,4)
R=lambda p:(p[2],p[0],p[1])
assert tuple(R(c) for c in satellites)==satellites[1:]+satellites[:1]
assert R(R(R((1,2,3))))==(1,2,3)

# REPAIR (2026-10-24): old t in [1,8] touched unit-ball
# boundaries only at isolated points. That was NOT an attachment!
# Use genuine radius-eps tubes with centreline t in [1/2,17/2].
# Both complete endpoint disk sections are strictly INSIDE their
# respective unit balls (positive-volume attaching overlap).
start,end=Q(1,2),Q(17,2)
assert start**2+eps**2 == Q(5,16) < 1
assert (Q(9)-end)**2+eps**2 == Q(5,16) < 1
# If any point of a tube is outside the central unit ball,
# its axial t must exceed 3/4: t<=3/4 would imply
# norm^2<= (3/4)^2+(1/4)^2=5/8<1.
# At a shared point of tubes on distinct axes, the other tube
# requires that same coordinate <=eps=1/4. Contradiction.
assert Q(3,4)**2+eps**2 == Q(5,8) <1
assert Q(3,4)>eps
# Each tube remains separated from the two nonincident satellites:
# its transverse coordinate has absolute value <= eps, whereas an
# off-axis satellite has transverse coordinate 9.
assert (Q(9)-eps)**2>1
# Unit centre and three unit satellites are pairwise disjoint.
assert Q(81)>4 and Q(162)>4

vertices=('central',0,1,2)
edges=(('central',0),('central',1),('central',2))
assert len(vertices)==4 and len(edges)==len(vertices)-1
assert {'central'}|{b for a,b in edges}==set(vertices)
assert {('central',(b+1)%3) for a,b in edges}==set(edges)

print('PASS exact C3 star: positive-volume collar overlap at BOTH ball endpoints')
print('PASS exposed radius-1/4 tubes are pairwise disjoint outside central ball')
print('PASS four vertices, three edges, connected acyclic star and equivariance')
print('CONDITIONAL topology: collared boundary-connected sum along a tame tree gives B3')
print('OPEN: actual wild horned satellite embeddings/collars, geometric van Kampen and pi1')
