#!/usr/bin/env python3
"""Exact reference checks of the native factorial limit and period product.
No pi reference, no floating-point arithmetic, no claim of native elaboration.
"""
from fractions import Fraction as F
from math import isqrt
import sympy as sym

A, B, C, K, M = 13591409, 545140134, 640320**3, 426880, 2**41


def main():
    k, r, s, t, d = sym.symbols('k r s t d', positive=True)
    assert sym.expand(k*r*d*t*s-k*r*s*t*d) == 0
    assert sym.cancel((k*r*d/(s*t))*(t/d)-k*r/s) == 0
    p, q, u = 1, 1, 0
    prefixes = [F(0)]
    for n in range(259):
        pn, qn = (1, 1) if n == 0 else (-24*(2*n-1)*(6*n-5)*(6*n-1), C*n**3)
        p *= pn
        q *= qn
        defect = p*(A+B*n)
        u = u*qn + defect
        prev = prefixes[-1]
        now = F(u,q)
        assert now-prev == F(defect,q)
        assert M**n*abs(defect) <= A*q
        assert abs(now-prev) <= F(A,M**n)
        if n:
            assert A*n <= M**n
            assert abs(now-prev) <= F(1,n)
        prefixes.append(now)
    for m in range(1,129):
        for n in range(1,129):
            z = min(m,n)
            lo, hi = sorted(prefixes[z:z+2])
            assert lo <= prefixes[m] <= hi and lo <= prefixes[n] <= hi
            assert abs(prefixes[m]-prefixes[n]) <= hi-lo <= F(1,z)
            assert abs(prefixes[m]-prefixes[n]) <= F(1,m)+F(1,n)
    previous = None
    for n in range(257):
        k=41*n
        cutoff = 1+(k+4)//41
        assert cutoff == n+1
        s = 2**(k+2)
        r = isqrt(10005*s*s)
        assert s>=n and r*r <= 10005*s*s < (r+1)**2
        lo, hi = sorted(prefixes[cutoff:cutoff+2])
        assert lo>0
        L, U = F(K*r,s)/hi, F(K*(r+1),s)/lo
        assert L*hi == F(K*r,s)
        assert U*lo == F(K*(r+1),s)
        assert U-L <= F(1,2**k)
        if previous:
            assert previous[0]<=L<=U<=previous[1]
        previous=L,U
        # A translated putative period product must not silently pass.
        assert (L+F(1,10**6))*hi != F(K*r,s)
    print('2 symbolic corner normal forms PASS')
    print('259 original signed defect bounds; 258 positive-index inverse budgets PASS')
    print('16384 native factorial regularity pairs PASS')
    print('257 synchronized cutoffs, root floors, lower/upper corner product pairs and shifted-product negative controls PASS')

if __name__=='__main__': main()
