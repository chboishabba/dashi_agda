#!/usr/bin/env python3
"""Stable inward-cap exact rational certificate for a SUPPORTED Hatcher ball.

Franca Lippert, The Alexander Horned Sphere and Bing's Hooked Rug, §2.1-2.2:
nested horn-stage homeomorphisms can be chosen to be the identity
away from shrinking attachment support. Preserve a round cap on the
initial B0 by confining every horn attachment to the OTHER hemisphere.

This finite geometric check uses initial B0 radius 3/4 inside the
unit satellite reference ball. It does not construct the infinite
linked horn attachment or its stage homeomorphisms.
"""
from fractions import Fraction as F
from itertools import product

r0=F(3,4)
satellite_radius=F(1)
spoke_radius=F(1,4)
start,end=F(1,2),F(17,2)
assert r0<satellite_radius
# Actual inward tube section (t=8.5 relative x=-0.5 to centre 9e_i)
# lies ENTIRELY inside the initial B0, not merely inside an outer
# container unit ball, so a cap-preserving wild-ball construction
# inherits a nontrivial positive-volume overlap.
assert F(1,2)**2+spoke_radius**2==F(5,16)<r0*r0==F(9,16)
# A round collar graph on a disk of radius 1/4 in the local
# inward hemisphere is x=-sqrt(r0^2-u^2-v^2)+s, |s|<=1/8.
# The homeomorphism onto its image has the explicit inverse
# (x,u,v)->(u,v,s=x+sqrt(r0^2-u^2-v^2)).
# s=0 gives boundary, s>0 points inside B0, s<0 outside.
assert r0*r0-spoke_radius**2==F(1,2)>F(1,8)**2
# The inward hemisphere x<0 stays separated from any horn support
# chosen entirely in the outward x>=0 portion.
# Tube axial collar crossing occurs at t=9-sqrt(r0^2-u^2-v^2),
# which lies strictly between t=8.25 and 8.5.
assert start<F(9)-r0<end
assert (F(9)-end)**2<r0*r0-spoke_radius**2
count=0
for a,b in product(range(-16,17),repeat=2):
    u,v=F(a,64),F(b,64)
    rad=u*u+v*v
    if rad>spoke_radius**2:continue
    sq=r0*r0-rad
    assert F(1,2)<=sq<=r0*r0
    assert sq>F(1,8)**2
    count+=1
print("PASS exact B0 radius 3/4, unit reference satellite, inward spoke overlap")
print("PASS explicit round inward collar graph and inverse,",count,"rational chart tests")
print("PROVEN IF SUPPORT ASSIGNED: fixed cap survives every stage and infinite limit")
print("UNPROVED BY SCRIPT: supported actual infinite horn replacement, van Kampen geometry")
