#!/usr/bin/env python3
"""Independent exact universal-formula signed orbit parity regression.

The Agda theorem YMClayRationalS3OddSignOrbitCancellationExact uses
the full sixteen-element sign orbit as a MULTISET. This checks all
integer exponent vectors 0..7 and rational sample coordinates,
including zeros/stabilizer duplications. The universal Agda source
proof uses oddPower/evenPower induction, not these samples.

Attribution: original DASHI SU2/hyperoctahedral owners, Weyl/Reynolds.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod

nodes=(
 (Q(1,3),Q(-2,5),Q(3,7),Q(0)),
 (Q(0),Q(1,2),Q(1,2),Q(-1,2)),
 (Q(1),Q(0),Q(0),Q(0)),
 (Q(2,7),Q(3,11),Q(-4,13),Q(5,17)),
)
tested=0
for q in nodes:
 for exponents in product(range(8),repeat=4):
  actual=sum((
   prod((sign*q[i])**exponents[i] for i,sign in enumerate(signs))
   for signs in product((-1,1),repeat=4)
  ),Q(0))
  expected=(Q(0) if any(e%2 for e in exponents) else
            16*prod(q[i]**exponents[i] for i in range(4)))
  assert actual==expected,(q,exponents,actual,expected)
  tested+=1
assert tested==len(nodes)*8**4
print("YM_S3_ALL_DEGREE_SIGN_ORBIT_PARITY_PASS",tested)
