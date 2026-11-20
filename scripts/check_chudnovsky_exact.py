#!/usr/bin/env python3
"""Exact Chudnovsky rational certificate; classical identity is external.
Attribution: D. V. and G. V. Chudnovsky; reuse DASHI P/Q/B/T recurrence.
"""
from fractions import Fraction as F
from math import factorial, isqrt
from time import perf_counter
from statistics import median
A,B,C=13591409,545140134,640320**3

def split(a,b):
    if a==b:return 1,1,1,0
    if b-a==1:
        p,q=(1,1) if a==0 else (-24*(2*a-1)*(6*a-5)*(6*a-1),C*a**3)
        return p,q,1,(A+B*a)*p
    m=(a+b)//2
    p,q,d,t=split(a,m); P,Q,D,T=split(m,b)
    return p*P,q*Q,d*D,t*Q*D+p*d*T

def interval(n,bits):
    assert n>=1 and bits>=1
    p,q,d,t=split(0,n)
    v=F(t,q*d)
    nxt=F(p,q)*F(-24*(2*n-1)*(6*n-5)*(6*n-1),C*n**3)*(A+B*n)
    lo,hi=sorted((v,v+nxt)); assert lo>0
    scale=1<<bits; z=isqrt(10005*scale**2)
    return F(426880*z,scale)/hi,F(426880*(z+1),scale)/lo

def atan(q,n):
    v=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),F(0))
    return sorted((v,v+F((-1)**n,(2*n+1)*q**(2*n+1))))

def check():
    assert A+B<42*A and 42*1728<C
    for n in range(1,15):
        p,q,d,t=split(0,n)
        assert F(t,q*d)==sum((F((-1)**k*factorial(6*k)*(A+B*k),factorial(3*k)*factorial(k)**3*C**k) for k in range(n)),F(0))
    a,b=atan(5,100); c,d=atan(239,40)
    l,u=interval(12,512)
    assert l<=16*b-4*c and 16*a-4*d<=u
    # Magnitude ratio bounded by 1728*42/C < 1, giving alternating bracket.
    for digits in (100,1000,3000,10000):
        n=digits//14+2; bits=4*digits+32
        samples=[]
        for _ in range(7):
            st=perf_counter(); l,u=interval(n,bits); samples.append(perf_counter()-st)
        assert u-l<=F(1,10**digits)
        print(digits,n,median(samples)*1000)
if __name__=='__main__':check()
