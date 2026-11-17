#!/usr/bin/env python3
"""Rational interval certificate for sin(n) using Machin pi and phase reduction.

pi/4 = 4 atan(1/5) - atan(1/239); each arctangent bracket comes
from alternating series, with rational endpoint bounds.
Let q in Z, r=n-2*pi*q. An interval for pi gives exact bounds for r.
At rational centre c, |sin(r)-Taylor_m(c)| <= |r-c|
 + |c|^(2m+3)/(2m+3)! (1-Lipschitz sine and Taylor theorem).
Return a sign only when the rational interval excludes zero.

Unlike Taylor around gigantic n, the local Taylor degree depends on
reduced phase, but pi precision must still resolve q*pi. Thus this
algorithm does NOT efficiently decide sin(99^(9999!)).
"""
from fractions import Fraction as F
from math import factorial
from sys import argv

def atan_interval(recip, terms):
    x=F(1,recip)
    s=F(0)
    for k in range(terms):
        s+=(-1)**k*x**(2*k+1)/F(2*k+1)
    nextterm=x**(2*terms+1)/F(2*terms+1)
    return (s, s+nextterm) if terms%2==0 else (s-nextterm,s)

def pi_interval(terms):
    a,b=atan_interval(5,terms)
    c,d=atan_interval(239,terms)
    return 16*a-4*d,16*b-4*c

def nearest_int(x):
    return (x+F(1,2)).numerator//(x+F(1,2)).denominator

def phase_interval(n,terms):
    lower,upper=pi_interval(terms)
    mid=(lower+upper)/2
    q=nearest_int(F(n)/(2*mid))
    endpoints=(F(n)-2*q*lower,F(n)-2*q*upper)
    lo,hi=min(endpoints),max(endpoints)
    return q,lo,hi

def taylor_sine(c,terms):
    s=F(0)
    for k in range(terms):
        s+=(-1)**k*c**(2*k+1)/factorial(2*k+1)
    radius=abs(c)**(2*terms+1)/factorial(2*terms+1)
    return s,radius

def certify(n,pi_terms=16,sin_terms=20):
    if n<=0: raise ValueError("n must be positive")
    q,lo,hi=phase_interval(n,pi_terms)
    mid=(lo+hi)/2
    uncertainty=(hi-lo)/2
    approx,err=taylor_sine(mid,sin_terms)
    lower,upper=approx-err-uncertainty,approx+err+uncertainty
    if lower>0:sign=1
    elif upper<0:sign=-1
    else:sign=0
    return sign,q,lower,upper

if __name__=="__main__":
    n=int(argv[1]) if len(argv)>1 else 99
    pi_terms=int(argv[2]) if len(argv)>2 else 24
    sin_terms=int(argv[3]) if len(argv)>3 else 24
    sign,q,lo,hi=certify(n,pi_terms,sin_terms)
    print("n:",n,"winding:",q)
    print("exact rational bounds:",lo,hi)
    print("CERTIFIED SIGN" if sign else "INCONCLUSIVE",sign)
    if not sign: raise SystemExit(2)
