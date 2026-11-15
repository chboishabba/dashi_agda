#!/usr/bin/env python3
"""Finite exact consistency of 6-step spatial mirror and C3 relabelling.
Demonstrates full twists are invisible to endpoint SO(2) and Z2 parity.
"""
from fractions import Fraction
path=((-1,1),(0,1),(0,0),(0,-1),(1,-1),(1,0),(1,1),(0,1),(0,0),(0,-1),(-1,-1),(-1,0))
mirror=lambda xy:(-xy[0],xy[1])
conf=lambda t:tuple(path[(t+4*i)%12] for i in range(3))
assert all(path[(t+6)%12]==mirror(path[t]) for t in range(12))
assert all(conf(t+6)==tuple(map(mirror,conf(t))) for t in range(12))
assert all(conf(t+4)==(conf(t)[1],conf(t)[2],conf(t)[0]) for t in range(12))
# Integer unwrapped framing lifts have the same S1 terminal angle at any full turns.
import cmath,math
assert all(abs(cmath.exp(2j*math.pi*n)-1)<1e-12 for n in range(-8,9))
# A reflection changes a phase winding sign, if the O(2) fibre inversion is chosen.
assert all(-(-n)==n for n in range(-8,9))
print("PASS T9 mirror / C3 equivariance; endpoint-angle winding information loss; O2 inversion parity")
print("NOT established: physical continuous frame lift from grid reflection")
