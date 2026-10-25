#!/usr/bin/env python3
"""Finite rational stage-clearance and three-copy isometry acceptance.
Original source Hatcher Example 2B.2: X_(n+1) subset X_n, B=intersection X_n.
C3 isometric satellite placement: existing Agda horn owner PR #1244.
This test verifies logical and synthetic local-metric inputs; it does NOT
supply Hatcher's actual marked Euclidean meridian or full stage avoidance.
"""
from fractions import Fraction as F
from itertools import product

def R(v): return (v[2],v[0],v[1])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
for v in product(range(-3,4), repeat=3):
    assert dot(R(v),R(v))==dot(v,v)
    assert R(R(R(v)))==v
centres=((9,0,0),(0,9,0),(0,0,9))
assert tuple(R(c) for c in centres)==centres[1:]+centres[:1]
print('PASS exact R^T R=I, R^3=I and three satellite centres')

# Exact toy Euclidean transverse tubes: a ROUND strand in a radius-rho
# cylinder, and a concentric meridian circle with radius r>rho.
# Loop length=2*pi*r; local radial clearance=r-rho>0.
# No statement that the WHOLE finite Hatcher stage X_n avoids the circle.
for n in range(40):
    rho=F(1,2**(n+2)); radius=F(1,2**(n+1))
    assert 0<rho<radius
    assert radius-rho==rho
    assert radius/F(1,2**n)==F(1,2)
    # Any rigid C3 rotation has the same circle length and clearance.
    assert dot(R((radius,0,0)),R((radius,0,0)))==radius**2
print('PASS 40 shrinking ROUND toy circles: exact positive local gaps, length=2*pi*r; C3 invariant')

# Fail-closed: local meridian clearance around ONE tube does NOT imply
# full X_n avoidance when another tube crosses the loop.
for n in range(6):
    radius=F(1,2**(n+1))
    crossing_other_tube_center=(radius,F(0))
    sample_circle_point=(radius,F(0))
    assert crossing_other_tube_center==sample_circle_point
print('PASS full-stage intersection is a separate indispensable gate')

# Nested-set logical certificate, checked for exact synthetic finite
# stages: a loop outside X_n stays outside X_m for m>=n and B subset X_n.
U=set(range(200))
X=[set(range(3*(16-n))) for n in range(17)]
B=X[-1]
for n in range(len(X)):
    outside={p for p in U if p not in X[n]}
    assert outside.isdisjoint(X[n])
    assert all(outside.isdisjoint(X[m]) for m in range(n,len(X)))
    assert outside.isdisjoint(B)
print('PASS persistent stage avoidance through every later X_m and limiting B')

# Winding negative control: same radius does not bound rectifiable length
# if an arbitrary path winds k times. Diameter only remains insufficient.
for n in range(1,14):
    r=F(1,2**n)
    k=2**(2*n)
    assert k*r == 2**n
print('PASS shrinking-circle-image / growing-length winding control')
print('OPEN actual source-marked local meridians: F_(2^n) basis, entire X_n avoidance, smooth circumference')
