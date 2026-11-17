#!/usr/bin/env python3
"""Independent exact original scalar yy angular Gram radial measure tests.

This is NOT the full 3x3 TT tensor norm, nor a discrete FV tensor map.
Original KSW angular Legendre owner and related attribution retained.
"""
import sympy as s
mu,r,eps=s.symbols("mu r eps",positive=True)
ell=(0,2,4)
G={}
for l in ell:
    for m in ell:
        actual=s.integrate(s.legendre(l,mu)*s.legendre(m,mu),(mu,-1,1))
        target=s.Rational(2,2*l+1) if l==m else s.S.Zero
        assert s.simplify(actual-target)==0
        G[(l,m)]=actual
for l in ell:
    assert s.simplify(r*r*(r/eps)**(2*l)
                      -r**(2+2*l)*eps**(-2*l))==0
print("12/12 exact original Legendre Gram and effective radial measures passed")
