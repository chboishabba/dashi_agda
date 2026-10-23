#!/usr/bin/env python3
"""Invariant-radius comparison for local zero-angular-momentum observer dragging.
Boosted Kerr Einstein frame to first order in spin. Not full satellite nodal drift.
"""
import math
from scipy.optimize import brentq
GM=3.986004418e14
C=299792458.
M4=GM/C**2

def ratio(alpha, areal_radius):
    q=math.sinh(alpha)**2
    M=M4/(1+q/2)
    def H(r): return 1+2*M*q/r
    def area(r): return r*H(r)**.25
    r=brentq(lambda r: area(r)-areal_radius,areal_radius*.999999,areal_radius*1.000001)
    physical= (2/H(r))/r**3
    gr=2/areal_radius**3
    assert math.isclose(physical/gr,H(r)**(-.25),rel_tol=1e-12)
    return H(r)**(-.25)
for R in (7820e3,12270e3):
    for alpha in (0,.3,1):
        value=ratio(alpha,R)
        print(f"R={R/1e3:.0f} km, alpha={alpha}, local dragging ratio={value:.16f}, delta={value-1:+.9e}")
        if alpha==0: assert value==1
print("PASS fixed-ADM-mass, fixed-J, fixed-areal-radius local dragging comparison")
print("NOT geodesic nodal drift, observational bound or physical Earth KK source")
