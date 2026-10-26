#!/usr/bin/env python3
"""Certified small-position BBP hex extractor through DASHI two punctured nines.

External source: Bailey--Borwein--Plouffe 1995 π digit-extraction identity.
Finite carrier: DASHI OggSSPP2BalancedTernaryPuncturedPlaneExact (8 points).
The chosen two-sheet labelling transports Z/16 arithmetic. It does NOT
identify the native antipodal action with hexadecimal negation.
No polynomial-in-log(position) algorithm or original Pickover sign is claimed.
"""
from fractions import Fraction
from math import factorial

POINTS=('negativeFirstAxis','positiveFirstAxis','negativeSecondAxis',
        'positiveSecondAxis','negativeEqualDiagonal','positiveEqualDiagonal',
        'negativeOppositeDiagonal','positiveOppositeDiagonal')
def sheet(n):
    assert 0<=n<16
    return divmod(n,8)
def glyph(n):
    s,p=sheet(n)
    return (s,POINTS[p])
def carry_add(a,b):
    sa,pa=sheet(a);sb,pb=sheet(b)
    t=pa+pb
    return 8*((sa+sb+t//8)%2)+t%8
def mul(a,b):
    # Arithmetic transported across the codec, not native geometric product.
    return (a*b)%16

def fractional_bbp(k,extra=12):
    """Exact fractional part of truncated 16^k*pi BBP sum."""
    acc=Fraction(0)
    count=0
    for j in range(k+extra+1):
        v=Fraction(0)
        for coefficient,den_offset in ((4,1),(-2,4),(-1,5),(-1,6)):
            d=8*j+den_offset
            x=(Fraction(pow(16,k-j,d),d) if j<=k
               else Fraction(1,16**(j-k)*d))
            v+=coefficient*x
            count+=1
        acc=(acc+v)%1
    # Sum_{j>=k+extra+1} 8*16^{k-j} <= (8/15)*16^(-extra).
    err=Fraction(8,15*16**extra)
    return acc,err,count

def certified_hex_digit(k):
    for extra in (8,12,20,32):
        f,err,count=fractional_bbp(k,extra)
        low=f-err;high=f+err
        if 0<=low and high<1 and (16*low).numerator//(16*low).denominator==(16*high).numerator//(16*high).denominator:
            d=(16*low).numerator//(16*low).denominator
            return d,count,extra
    raise AssertionError('could not separate boundary; increase precision')

def main():
    for a in range(16):
        assert sheet(a)[0]*8+sheet(a)[1]==a
        for b in range(16):
            assert carry_add(a,b)==(a+b)%16
            assert mul(a,b)==a*b%16
    expect='243F6A88'
    for k,char in enumerate(expect):
        d,count,extra=certified_hex_digit(k)
        assert d==int(char,16),(k,d,char)
        print('index',k,'digit',char,'carrier',glyph(d),
              'BBP rational terms',count,'tail depth',extra)
    print('PASS: exact rational BBP digits, transported hex arithmetic, certified tail')
    print('COST: k-th digit uses >=4*(k+1) modular fractions in this BBP method')
    print('OPEN: no short remote-index digit extraction or 1/(2*pi) sine-sign witness')
if __name__=='__main__':main()
