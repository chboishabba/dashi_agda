#!/usr/bin/env python3
"""Exact no-wrap shift-two autocorrelation via cyclic group-ring Fourier duality.

For polynomial F(t)=sum f[n] t^n in Z[t]/(t^M-1):
  F(t)F(t^-1) coefficient at t^2 = sum_n f[n+2] f[n].
The group-ring convolution identity is the exact algebraic precursor to
DFT inversion; Fourier evaluation at Mth roots of unity is a ring map.
No floating-point FFT, no assumed asymptotic arithmetic theorem.
"""
from math import isqrt
def primes(N):
    sieve=[True]*(N+1)
    sieve[0:2]=[False,False]
    for p in range(2,isqrt(N)+1):
        if sieve[p]:
            for k in range(p*p,N+1,p):sieve[k]=False
    return sieve
def cyclic_product_at_shift(f,M,h):
    assert 0<=h<M
    return sum(f[i]*f[(i+h)%M] for i in range(M))
def linear_at_shift(f,h):
    return sum(f[i]*f[i+h] for i in range(len(f)-h))
def polynomial_laurent_coefficient(f,M,h):
    # Coefficient of t^h in F(t)F(t^-1) in the exact group ring.
    return sum(a*b for i,a in enumerate(f) for j,b in enumerate(f)
               if (i-j-h)%M==0)
def verify():
    for X in (12,30,70,101):
        isp=primes(X)
        f=[int(isp[k]) for k in range(X+1)]
        M=2*(X+1)+7
        padded=f+[0]*(M-len(f))
        direct=linear_at_shift(f,2)
        assert direct==sum(int(isp[n] and isp[n+2]) for n in range(2,X-1))
        assert cyclic_product_at_shift(padded,M,2)==direct
        # F(t) F(t^-1) at exponent -2 matches positive lag 2.
        assert polynomial_laurent_coefficient(padded,M,M-2)==direct
    # Cross-shell terms must survive; decomposing f=g+h requires 4 terms.
    g=[1,0,1,0,0,0,0]
    h=[0,1,0,1,0,0,0]
    M=len(g)
    f=[a+b for a,b in zip(g,h)]
    mixed=sum(g[i]*h[i+2]+h[i]*g[i+2] for i in range(M-2))
    assert linear_at_shift(f,2)==linear_at_shift(g,2)+linear_at_shift(h,2)+mixed
    print("PASS exact shifted cyclic group-ring correlation, no wrap, and mixed shells")
if __name__=="__main__":verify()
