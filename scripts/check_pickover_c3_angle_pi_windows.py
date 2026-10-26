#!/usr/bin/env python3
"""C3 equilateral-angle certified pi window and decimal-phase negative control.
Classical source: equilateral 60-degree angle pi=6 atan(1/sqrt(3)),
Gregory arctan alternating series; DASHI contribution: rational tests.
"""
from fractions import Fraction
from math import isqrt

def arctan_interval(x, n):
    total=sum(((-1)**k*x**(2*k+1)/Fraction(2*k+1) for k in range(n)),Fraction(0))
    rem=x**(2*n+1)/Fraction(2*n+1)
    return (total,total+rem) if n%2==0 else (total-rem,total)

def c3_pi_window(decimal_digits, terms=None):
    scale=10**(decimal_digits+5)
    q=isqrt(3*scale*scale)
    root_lo=Fraction(q,scale)
    root_hi=Fraction(q+1,scale)
    x_lo=1/root_hi
    x_hi=1/root_lo
    assert Fraction(0)<x_lo<x_hi<1
    n=terms or 3*(decimal_digits+10)
    lo=6*arctan_interval(x_lo,n)[0]
    hi=6*arctan_interval(x_hi,n)[1]
    return lo,hi,n

def sign_for_10pow(k):
    for precision in (k+15,k+30):
        a,b,n=c3_pi_window(precision)
        N=10**k
        qlo=(N*b.denominator)//b.numerator
        qhi=(N*a.denominator)//a.numerator
        if qlo==qhi:
            return (1 if qlo%2==0 else -1),n,precision
    raise AssertionError('pi precision insufficient')

def main():
    for k in (1,2,3,6,24,120):
        sign,n,precision=sign_for_10pow(k)
        print('10^',k,'sign',sign,'terms',n,'precision',precision)
    assert sign_for_10pow(120)[0]==-1
    print('PASS exact C3-angle pi brackets and base10 signed witnesses')
    print('OPEN: sublinear remote phase extraction and 99^(9999!)')
if __name__=='__main__':main()
