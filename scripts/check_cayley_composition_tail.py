#!/usr/bin/env python3
"""Finite Gaussian rational composition check; analytic transport is documented separately.
Reuse BishopMachinOriginalCayleyFormalSeriesExact's coefficient convention.
Coefficients represented as rational multiples of i**n (no second analytic carrier).
"""
from fractions import Fraction as F
from math import factorial
from time import perf_counter


def mul(a,b,N):
    return [sum((a[j]*b[k-j] for j in range(k+1)),F(0)) for k in range(N+1)]


def nested(N):
    # 2i atan(X) coefficient divided by i**k is 2/k for odd k.
    a=[F(2,k) if k%2 else F(0) for k in range(N+1)]
    power=[F(1)]+[F(0)]*N
    out=power[:]
    for m in range(1,N+1):
        power=mul(power,a,N)
        out=[x+y/factorial(m) for x,y in zip(out,power)]
    return out


def recurrence(N):
    # Exp chain coefficient rule: n*c_n=2*sum(c_(n-k), odd k <= n).
    c=[F(1)]
    sums=[F(1),F(0)]
    for n in range(1,N+1):
        c.append(2*sums[1-n%2]/n)
        sums[n%2]+=c[-1]
    return c


def certificate(t,N):
    assert 0<=t<=F(1,2)
    # At rho=3/4, absolute nested sum <= exp(24/7) < 81.
    # Total-degree truncation error <= 81*(t/rho)**(N+1).
    c=recurrence(N)
    real=sum((c[k]*(-1)**(k//2)*t**k for k in range(0,N+1,2)),F(0))
    imag=sum((c[k]*(-1)**(k//2)*t**k for k in range(1,N+1,2)),F(0))
    tail=81*(4*t/3)**(N+1)
    cr,ci=(1-t*t)/(1+t*t),2*t/(1+t*t)
    # Independent finite Cayley geometric tail <= 2*t**(N+1)/(1-t).
    geom=2*t**(N+1)/(1-t)
    assert abs(real-cr)+abs(imag-ci)<=geom
    return tail+geom


if __name__=='__main__':
    start=perf_counter()
    for N in (0,1,2,8,16,32):
        assert nested(N)==recurrence(N)==[F(1)]+[F(2)]*N
    for q in (2,5,239):
        N=1
        while certificate(F(1,q),N)>F(1,10**40):
            N*=2
        print(q,N,'error <=',float(certificate(F(1,q),N)))
    print('PASS finite nested coefficients and rational tail budgets',perf_counter()-start)
