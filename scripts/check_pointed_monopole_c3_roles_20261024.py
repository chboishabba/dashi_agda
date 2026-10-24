#!/usr/bin/env python3
"""Pointed north/south U(1) patches -> physical spin-c magnetic flux index.

Standard Dirac/Chern quantization, not a derivation of a three-plasma source.
A 2D puncture winding, a Pin lift, a pointed marked centre, and a nonzero
first Chern class of a 4D Maxwell bundle are distinct typed physical claims.
"""
import math, cmath
from scipy.integrate import quad

for q in (0,3,10,11,12,13,24):
    # A_N = (q/2)(1-cos theta)dphi, A_S=-(q/2)(1+cos theta)dphi.
    flux=quad(lambda theta:math.pi*q*math.sin(theta),0,math.pi)[0]
    assert abs(flux/(2*math.pi)-q)<1e-11
    assert abs(cmath.exp(2j*math.pi*q)-1)<1e-11
    C3=cmath.exp(2j*math.pi*q/3)
    assert (abs(C3-1)<1e-11)==(q%3==0)
# Ordinary R3 minus three balls: H1=0, H2=Z^3; flux on each
# sphere bounding a region of smooth divB=0 vanishes.
# Existing two-ended R x S² slice: H2=Z, a nonbounding S² can
# carry a source-free flux (Misner/Wheeler 'charge without charge').
print('PASS: q is integral bundle flux and C3 patch phase only sees q mod 3')
print('NO: q=12/24 selected by C3; q=3 is equally trivial on this C3 phase')
print('NO: three ordinary plasma balls generate a net monopole flux')
print('OPEN: a physical smooth EM/topological field map from moving regions to the selected spin-c bundle')
