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

# Straight spoke skeletons t*e_i for 1<=t<=8. Distinct
# skeletons have distance^2=t^2+s^2>=2>(2eps)^2,
# so radius-eps tubes outside the central ball do not meet.
assert Q(2)>(2*eps)**2
# Every spoke is >=9 units from any OFF-AXIS satellite centre.
assert Q(81)>(Q(1)+eps)**2
# Unit centre and three unit satellites are pairwise disjoint.
assert Q(81)>4 and Q(162)>4

vertices=('central',0,1,2)
edges=(('central',0),('central',1),('central',2))
assert len(vertices)==4 and len(edges)==len(vertices)-1
assert {'central'}|{b for a,b in edges}==set(vertices)
assert {('central',(b+1)%3) for a,b in edges}==set(edges)

print('PASS exact C3 axis-spoke geometry: radius 1/4 tubes and rational gaps')
print('PASS four vertices, three edges, connected acyclic star and equivariance')
print('CONDITIONAL topology: collared boundary-connected sum along a tame tree gives B3')
print('OPEN: actual wild horned satellite embeddings/collars, geometric van Kampen and pi1')
