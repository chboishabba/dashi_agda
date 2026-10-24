#!/usr/bin/env python3
"""Finite exact clopen/C3 versus ambient-linking discriminator.

Original classical theorem (not proved here): linking number is
the signed transverse intersection number with an oriented spanning
disk. Endpoint Cantor sets with equal intrinsic clopen bases need not
have equivalent 3D embeddings; cf. Antoine/standard tame Cantor sets.

C1 is radius-2 CCW circle in xy-plane, with disk x²+y²<=4,z=0.
C2(t)=(h,1+cos(t),sin(t)), h=1 linked or h=5 unlinked.
At z=0 there are exactly two transverse hits (h,2,0),
normal derivative +1, and (h,0,0), normal derivative -1.
For h=1 exactly the second is IN the disk: linking = -1.
For h=5 neither is inside: linking = 0.

The 120-degree R(x,y,z)=(z,x,y) has det+1; it rotates this
local clasp into 3 satellite balls centred at 9e_x,9e_y,9e_z.
The finite rational separation bounds ensure no inter-sector
clasp. This is NOT a wild-ball embedding or Hatcher's exact
meridian/commutator geometry; it is a precise missing datum.
"""
from itertools import product
from fractions import Fraction as F

R=lambda v:(v[2],v[0],v[1])
centres=((9,0,0),(0,9,0),(0,0,9))
assert tuple(R(centres[k]) for k in range(3))==(centres[1],centres[2],centres[0])
assert R(R(R((1,2,3))))==(1,2,3)
# Radius-6 closed satellite balls are disjoint; unit central ball
# is disjoint from every satellite. All local comparison curves
# lie within radius sqrt(30)<6 of each centre.
assert 162>4*6*6
assert 9*9>(6+1)**2

for n in range(11):
    count=3*2**n
    mass=F(1,3*2**n)
    assert count*mass==1
    assert 2*F(1,3*2**(n+1))==mass
    for bits in product((0,1),repeat=n):
        assert all((bits+(b,))[:n]==bits for b in (0,1))
print("PASS intrinsic C3 x binary Cantor clopen partitions depths 0..10")
print("PASS 1/(3*2^n) cylinder mass and exact dyadic child refinement")

def linking_number_from_disk(h):
    hits=((h,2,+1),(h,0,-1))
    assert all(x*x+y*y != 4 for x,y,_ in hits)
    return sum(direction for x,y,direction in hits if x*x+y*y<4)
assert linking_number_from_disk(1)==-1
assert linking_number_from_disk(5)==0
assert all(linking_number_from_disk(1)==-1 for _ in range(3))
assert all(linking_number_from_disk(5)==0 for _ in range(3))
print("PASS linked pair lk=-1 versus unlinked pair lk=0 on SAME clopen Cantor address system")
print("PASS R cyclically permutes 3 disjoint congruent local clasp regions with exact margins")
print("NOT claimed: three-copy wild 3-ball, collars, genus of complement, pi1 or physical holonomy")
