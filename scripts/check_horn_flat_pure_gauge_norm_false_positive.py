#!/usr/bin/env python3
"""Flat SU3 gauge-frame false-positive control; exact symbolic calculations.

For punctured-plane polar coordinates (r,theta), n positive integer:
 g_n(theta)=diag(exp(i*n*theta), exp(-i*n*theta),1) lies in SU3.
 A_n=g_n^{-1}dg_n=diag(i*n,-i*n,0) dtheta.
 It has F=dA+A wedge A=0 and Hol(circle)=I.
 Yet the operator norm coefficient in an orthonormal angular frame
 is n/r, unbounded as r->0 and as n->infinity.
 A_n is gauge-equivalent to zero by a smooth SINGLE-VALUED g_n.

This is a negative control against interpreting growth of a GAUGE
POTENTIAL norm as a physical curvature singularity. The positive
sibling-adaptive source theorem excludes a uniformly bounded
COMPATIBLE GAUGE presentation when the genuine source geometric
hypotheses hold; it does not imply gauge-invariant F divergence.

Classical U(1)/SU(3) gauge covariance; related original topology
source Hatcher Ex.2B.2, selected W owner neutrino PR #1247.
"""
from fractions import Fraction as F
import sympy as s

theta=s.symbols('theta',real=True)
I=s.I
for n in (1,2,3,7):
    g=s.diag(s.exp(I*n*theta),s.exp(-I*n*theta),1)
    ginv=s.diag(s.exp(-I*n*theta),s.exp(I*n*theta),1)
    assert s.simplify(g.det()-1)==0
    assert all(s.simplify(z)==0 for z in (g*ginv-s.eye(3)))
    dthetaA=s.simplify(ginv*g.diff(theta))
    assert dthetaA == s.diag(I*n,-I*n,0)
    # A_r=0, A_theta constant: F_{r,theta}=d_r Atheta
    # -d_theta Ar+[Ar,Atheta]=0.
    assert all(z==0 for z in dthetaA.diff(theta))
    hol=s.diag(s.exp(-2*s.pi*I*n),s.exp(2*s.pi*I*n),1)
    assert all(s.simplify(z)==0 for z in (hol-s.eye(3)))
    for depth in (0,1,3,6):
        r=F(1,2**depth)
        M=F(n)/r
        assert M==n*2**depth
print('PASS exact smooth single-valued SU3 pure gauge: F=0, Hol=I, unbounded |A|=n/r')
print('FAIL-CLOSED: norm growth is not a gauge-invariant curvature or energy statement')
