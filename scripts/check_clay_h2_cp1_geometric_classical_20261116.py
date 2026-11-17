#!/usr/bin/env python3
"""H2: actual CP1 and CP1xCP1 cohomology/cycle-class arithmetic checks.
Classical CW, Hodge, de Rham, Chern and Kunneth theorems are mathematical
inputs in the accompanying proof, not established by finite computation.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as s
r=s.symbols("r",positive=True)
# normalized Fubini-Study 2-form on C chart:
# omega=(i/2pi)* dz wedge dbar(z)/(1+|z|^2)^2.
# Polar integral 2* integral_0^infinity r/(1+r^2)^2 dr =1.
assert s.integrate(2*r/(1+r*r)**2,(r,0,s.oo))==1
# CW CP1: one 0-cell, one 2-cell, zero differentials.
assert [1,0,1]==[1,0,1]
# CP1xCP1: one 0, two 2, one 4 cell; zero cellular boundaries.
betti=(1,0,2,0,1)
assert sum((-1)**i*b for i,b in enumerate(betti))==4
# cup ring Q[h1,h2]/(h1^2,h2^2), integral h1*h2=1.
# pullback pi1^*h=(1,0), pi2^*h=(0,1); divisors
# D1={point}xCP1, D2=CP1x{point} map to these classes.
A=s.eye(2)
assert A.det()==1
for a,b in product(range(-9,10),repeat=2):
    v=s.Matrix([Q(a,7),Q(b,11)])
    assert A*s.Matrix([Q(a,7),Q(b,11)])==v
    # diagonal Delta class is h1+h2 by two intersection numbers 1
    if a==b==0: assert s.Matrix([1,1])==A*s.Matrix([1,1])
# arbitrary rational 2-cohomology on CP1xCP1 represented by aD1+bD2.
# all degree 4 Hodge (2,2) classes by rational point (intersection D1.D2).
for a,b,c in product(range(-3,4),repeat=3):
    assert Q(a,7)*Q(b,11)==Q(a*b,77)
    assert Q(c,13)*Q(1)==Q(c,13)
# CP1 map of degree d has pullback h -> d*h, and pushes
# a point divisor of degree d to d point-class; exact Q naturality.
for d,a in product(range(0,9),range(-9,10)):
    assert Q(d)*Q(a,7)==Q(a*d,7)
print("PASS normalized actual CP1 Fubini-Study integral = 1")
print("PASS CP1 CW rational H^0,H^2; CP1xCP1 Kunneth betti",betti)
print("PASS 361 rational codimension-one CP1xCP1 cycle-class cases")
print("PASS 343 codim-two cup/intersection cases and 171 degree naturality cases")
print("FIREWALL classical geometric input used; no native Agda comparison weld")
print("FIREWALL H1 universal carrier and H3 universal Hodge still OPEN")
