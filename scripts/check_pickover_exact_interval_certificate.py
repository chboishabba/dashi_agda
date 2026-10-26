#!/usr/bin/env python3
"""Exact phase-interval sign certificate (integer/rational only).

Given rational pi bounds PL<=pi<=PU, 99^k/PU<=99^k/pi<=99^k/PL.
Equal endpoint floors certify sign(sin(99^k)) by parity; never
promote the 101 torsion projection to a REAL sine-sign certificate.
"""
from fractions import Fraction
from math import factorial

def sign_certificate(k,pl,pu):
    assert 0<pl<=pu
    n=99**k
    a,b=Fraction(n,1)/pu,Fraction(n,1)/pl
    low=a.numerator//a.denominator
    high=b.numerator//b.denominator
    return (1 if low%2==0 else -1) if low==high else None

def machin_pi_bounds(k,spare=24):
    scale=99**(k+spare)
    def atan(q):
        j,p,sgn,total=0,q,1,0
        while True:
            term=scale//((2*j+1)*p)
            if term==0:return total,j
            total+=sgn*term
            j+=1;p*=q*q;sgn=-sgn
    a,na=atan(5);b,nb=atan(239)
    mid=16*a-4*b
    eps=16*(na+2)+4*(nb+2)
    return Fraction(mid-eps,scale),Fraction(mid+eps,scale)

def first_digit(k,pl,pu):
    a,b=Fraction(99**k,2*pu),Fraction(99**k,2*pl)
    ai,bi=a.numerator//a.denominator,b.numerator//b.denominator
    if ai!=bi:return None
    a,b=99*(a-ai),99*(b-bi)
    ai,bi=a.numerator//a.denominator,b.numerator//b.denominator
    return ai if ai==bi else None

def main():
    expected=(-1,-1,1,1,-1,1,-1)
    for n,expected_sign in enumerate(expected,1):
        k=factorial(n)
        pl,pu=machin_pi_bounds(k)
        sign=sign_certificate(k,pl,pu)
        digit=first_digit(k,pl,pu)
        assert sign==expected_sign
        assert digit is not None and digit!=49
        assert sign==(1 if digit<49 else -1)
        if n==7: assert digit==51
        print(f'{n}! exponent={k} first_radix99_digit={digit} signed={sign}')
    assert pow(99,120,101)==pow(99,720,101)==95
    print('PASS: seven exact real-phase sign certificates')
    print('PASS: 101 torsion observer loses the real sign on factorial subsequence')
    print('OPEN: 9999! real-phase interval or an alternative sublinear certificate')

if __name__=='__main__':main()
