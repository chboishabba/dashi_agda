#!/usr/bin/env python3
"""Exact finite signed covariance and Fourier interference comparisons.
Reuses NS ABCD centering algebra, not NS physical Navier–Stokes estimates.
"""
import sympy as s
rates=[s.Rational(1),s.Rational(3),s.Rational(5)]
work=[s.Rational(2),s.Rational(-3),s.Rational(1)]
n=len(rates)
rw=sum(a*b for a,b in zip(rates,work))
r=sum(rates); w=sum(work)
pair=sum((rates[i]-rates[j])*(work[i]-work[j])
         for i in range(n) for j in range(i+1,n))
assert s.simplify(n*(-rw)+r*w+pair)==0
assert w==0
# Pairwise signed optical interference is *not* a probability.
a=s.Matrix([1,-1,s.I])
coherent=s.expand(sum(a)*s.conjugate(sum(a)))
incoherent=sum(v*s.conjugate(v) for v in a)
cross=s.expand(coherent-incoherent)
assert s.simplify(coherent-incoherent-cross)==0
assert coherent==1 and incoherent==3 and cross==-2
print("PASS NS signed pair-difference centering (n=3) and coherent cross terms")
print("SIGNED WORK != photon count probability; no borrowed NS physical decay bound")
