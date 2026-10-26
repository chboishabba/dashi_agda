#!/usr/bin/env python3
"""Exact ninth-power non-descent. Machin's 1706 pi identity and alternating
arctangent brackets are classical; DASHI contributes the witness selection.
No terminal 9999! sine sign is asserted."""
from fractions import Fraction
def atan_bounds(q,t):
    v=sum(((-1)**j*Fraction(1,(2*j+1)*q**(2*j+1)) for j in range(t)),Fraction())
    e=Fraction(1,(2*t+1)*q**(2*t+1))
    return (v,v+e) if t%2==0 else (v-e,v)
def certify(k):
    n=99**k
    for t in (15,25,40,70,110):
        a,A=atan_bounds(5,t);b,B=atan_bounds(239,max(2,t//5))
        L,U=16*a-4*B,16*A-4*b
        x=n*U.denominator//U.numerator
        y=n*L.denominator//L.numerator
        if x==y:
            assert x*U<n<(x+1)*L
            return x,1 if x%2==0 else -1
    raise AssertionError('insufficient rational pi precision')
def main():
    a,sa=certify(9);b,sb=certify(18)
    assert (sa,sb)==(-1,+1)
    assert a==290781571073447469
    assert b==265633980425984427859213880941867086
    for k in (9,18):
        n=99**k
        assert n==(99**(k//9))**9
        assert n%3**9==0
    print('PASS: perfect ninth-power / Eisenstein-nilpotent collision')
    print('99^9:',a,sa,'99^18:',b,sb)
    print('PASS: opposite *certified* real sine signs')
    print('OPEN: original 9999!-exponent real-phase sign')
if __name__=='__main__':main()
