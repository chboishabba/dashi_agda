#!/usr/bin/env python3
"""Exact dyadic certificate for the class-number-one CM value at D=-163.

Numerical acceptance uses ONLY integers and Python Fraction for exact Machin
arctan prefixes. No float enters a predicate. It proves that the classical
q-series j(tau163) lies in the open half-integer window around -640320**3,
*conditional on* the classical q-series/period definitions.

With the classical CM-integrality theorem and the reduced-form class-one
theorem, the half-integer enclosure identifies the actual j-value exactly.
Those analytic and CM theorems are NOT proved by this Python checker or
automatically imported into Agda.

Sources: Serre, A Course in Arithmetic; Miyake, Modular Forms;
Apostol, Modular Functions and Dirichlet Series in Number Theory;
classical CM theorem / Hilbert class polynomials.
"""
from fractions import Fraction as F
from math import gcd, isqrt
from time import perf_counter
import argparse

def ceil_div(x, d):
    assert d != 0
    return -((-x)//d)

def atan_interval(q, terms):
    partial = sum((F((-1)**k, (2*k+1)*q**(2*k+1))
                   for k in range(terms)), F(0))
    term = F((-1)**terms, (2*terms+1)*q**(2*terms+1))
    return min(partial,partial+term),max(partial,partial+term)

def reduced_forms_minus_163():
    # For reduced positive definite forms: 3*a*a <= |D|=163.
    forms=[]
    for a in range(1, isqrt(163//3)+1):
        for b in range(-a,a+1):
            numerator=b*b+163
            if numerator%(4*a): continue
            c=numerator//(4*a)
            if a>c or gcd(a,gcd(abs(b),c))!=1: continue
            if (abs(b)==a or a==c) and b<0: continue
            assert b*b-4*a*c==-163
            forms.append((a,b,c))
    assert forms==[(1,1,41)], forms
    return forms

def make_interval(bits):
    scale=1<<bits
    class Interval:
        __slots__=("lo","hi")
        def __init__(self,lo,hi=None):
            self.lo=int(lo);self.hi=int(lo if hi is None else hi)
            assert self.lo<=self.hi
        @staticmethod
        def num(n):return Interval(n*scale)
        @staticmethod
        def rat(v):
            v=F(v)
            return Interval((v.numerator*scale)//v.denominator,
                            ceil_div(v.numerator*scale,v.denominator))
        def __add__(self,b):
            if isinstance(b,int):b=Interval.num(b)
            return Interval(self.lo+b.lo,self.hi+b.hi)
        __radd__=__add__
        def __neg__(self):return Interval(-self.hi,-self.lo)
        def __sub__(self,b):
            if isinstance(b,int):b=Interval.num(b)
            return self+(-b)
        def __mul__(self,b):
            if isinstance(b,int):
                return Interval(self.lo*b,self.hi*b) if b>=0 else Interval(self.hi*b,self.lo*b)
            candidates=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
            return Interval(min(candidates)//scale,
                            ceil_div(max(candidates),scale))
        __rmul__=__mul__
        def div_nat(self,n):
            assert n>0
            return Interval(self.lo//n,ceil_div(self.hi,n))
        def inv(self):
            assert self.lo>0 or self.hi<0
            return Interval((scale*scale)//self.hi,
                            ceil_div(scale*scale,self.lo))
        def __truediv__(self,b):return self*b.inv()
        def __pow__(self,n):
            assert n>=0
            result=Interval.num(1)
            for _ in range(n):result=result*self
            return result
    return Interval,scale

def exp_positive_interval(x, I, scale, terms=180):
    assert x.lo>=0 and 2*x.hi < (terms+1)*scale
    term=I.num(1);partial=I.num(0)
    for k in range(terms):
        partial=partial+term
        term=(term*x).div_nat(k+1)
    # For k >= terms, successive term ratio <= x_upper/(terms+1)<1/2.
    return I(partial.lo,partial.hi+2*term.hi)

def certify(bits=256, exp_terms=180):
    started=perf_counter()
    reduced_forms_minus_163()
    I,scale=make_interval(bits)
    a=atan_interval(5,90)
    b=atan_interval(239,30)
    pi_lo=I.rat(16*a[0]-4*b[1]).lo
    pi_hi=I.rat(16*a[1]-4*b[0]).hi
    pi=I(pi_lo,pi_hi)
    assert 3*scale < pi.lo <= pi.hi < 4*scale

    square_root_floor=isqrt(163*scale*scale)
    sqrt163=I(square_root_floor,square_root_floor+1)
    x=pi*sqrt163
    expx=exp_positive_interval(x,I,scale,exp_terms)
    r=expx.inv()  # exp(-pi*sqrt(163)), outward-rounded
    assert r.lo>0 and 128*r.hi<scale
    q=-r       # tau=(1+i sqrt(163))/2 -> q=-exp(-pi sqrt(163))

    # Exact first three q-series coefficients:
    # sigma3: 1,9,28; sigma5: 1,33,244.
    e4=I.num(1)+240*(q+9*q**2+28*q**3)
    e6=I.num(1)-504*(q+33*q**2+244*q**3)
    # Bound sum_{n>=4} sigma_k(n) r^n via sigma_k(n)<=n^(k+1);
    # ratio of majorants <=2^(k+1)*r<=1/2 for k<=5.
    def tail(coeff,k):
        return ceil_div(2*coeff*4**(k+1)*r.hi**4,scale**3)
    t4=tail(240,3);t6=tail(504,5)
    e4=I(e4.lo-t4,e4.hi+t4)
    e6=I(e6.lo-t6,e6.hi+t6)
    disc=e4**3-e6**2
    assert disc.hi<0
    j=1728*(e4**3)/disc
    target=-640320**3
    assert target*scale-scale//2 < j.lo <= j.hi < target*scale+scale//2

    return {
       "bits":bits,
       "target":target,
       "reduced_forms_minus_163":[(1,1,41)],
       "j_lower_offset":F(j.lo-target*scale,scale),
       "j_upper_offset":F(j.hi-target*scale,scale),
       "width":F(j.hi-j.lo,scale),
       "wall_seconds":perf_counter()-started,
    }

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--bits",type=int,nargs="*",default=[128,160,256])
    args=parser.parse_args()
    for bits in args.bits:
        result=certify(bits)
        print("PASS exact dyadic j(-163) half-integer certificate",
              "bits=",bits,"target=",result["target"])
        print("  lower-minus-target =",result["j_lower_offset"])
        print("  upper-minus-target =",result["j_upper_offset"])
        print("  width approximately =",float(result["width"]))
        print("  elapsed seconds =",result["wall_seconds"])
    print("WARNING: CM integrality, source pi/exp identity and same-carrier Agda proof remain external obligations")

if __name__=="__main__":
    main()
