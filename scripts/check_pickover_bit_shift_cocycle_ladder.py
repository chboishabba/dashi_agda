#!/usr/bin/env python3
"""Exact binary-shift / phase cocycle ladder and BIDI discriminator audit.

Check shift-and-add vs popcount-vs-run signed-digit scalar addition chains
on an exact finite complex phase ring Z[i]/(2^w); no real-sine transfer
is claimed. Source: binary powering (classical); NAF (standard); DASHI
RSA/Shor and consumer-relative residual reuse. A ring can validate
powering identities even if it cannot determine the real phase sign.
"""
from math import factorial

def binary_chain(n):
    assert n>0
    return n.bit_length()-1+n.bit_count()-1

def naf_digits(n):
    out=[]
    while n:
        if n&1:
            d=2-(n%4)
            out.append(d); n-=d
        else: out.append(0)
        n//=2
    return out

def signed_chain(n):
    ds=naf_digits(n)
    return max(0,len(ds)-1)+max(0,sum(d!=0 for d in ds)-1)

def gaussian_mul(x,y,m):
    a,b=x;c,d=y
    return ((a*c-b*d)%m,(a*d+b*c)%m)

def gaussian_pow(x,n,m):
    r=(1,0)
    while n:
        if n&1:r=gaussian_mul(r,x,m)
        x=gaussian_mul(x,x,m)
        n>>=1
    return r

def ladder(x,n,m):
    # MSB to LSB: accumulator = accumulator^2 * x if next bit=1
    r=(1,0)
    for bit in bin(n)[2:]:
        r=gaussian_mul(r,r,m)
        if bit=='1':r=gaussian_mul(r,x,m)
    return r

def main():
    m=2**64
    x=(123,456)
    for n in [1,2,3,9,11,99,99**2,99**3,99**6,99**24]:
        assert gaussian_pow(x,n,m)==ladder(x,n,m)
        assert gaussian_pow(x,9*11,m)==gaussian_pow(gaussian_pow(x,9,m),11,m)
        assert gaussian_pow(x,9*11,m)==gaussian_pow(gaussian_pow(x,11,m),9,m)
        assert signed_chain(n)<=binary_chain(n)+1 or n==1
    E=factorial(9999)
    # Crucial: the exponent used by phase power is N=99^E, whose
    # bit count is proportional to E, not to bit_length(E).
    print('bits(E)',E.bit_length())
    print('bit_length(99^E) is between 6E+1 and 7E; E has','more than 30000','decimal digits')
    print('No expansion of 99^E was performed.')
    print('PASS: exact shift-bit complex-power coherence in finite Gaussian ring')
    print('BOUNDARY: 99^E binary ladder requires Theta(E) bit positions.')
    print('NAF may save selected multiplies but not the bit-position count.')
if __name__=='__main__':main()
