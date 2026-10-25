#!/usr/bin/env python3
"""Certified small factorial-position pi phases via Machin rationals.
John Machin: pi=16*atan(1/5)-4*atan(1/239).
No floating point; this deliberately DOES NOT determine sin(99^(9999!)).
"""
from math import factorial

def fixed_atan(scale, den):
    j,p,s,total=0,den,1,0
    while True:
        term=scale//((2*j+1)*p)
        if term==0:
            return total,j
        total+=s*term
        j+=1
        p*=den*den
        s=-s

def interval_pi(scale):
    a,na=fixed_atan(scale,5)
    b,nb=fixed_atan(scale,239)
    c=16*a-4*b
    e=16*(na+1)+4*(nb+1)
    return c-e,c+e

def digit_alpha(base,k,scale,L,U):
    lo=(pow(base,k)*scale)//(2*U)
    hi=(pow(base,k)*scale)//(2*L)
    assert lo==hi
    return lo%base

def certified_sin_sign(base,k,scale,L,U):
    lo=(pow(base,k)*scale)//U
    hi=(pow(base,k)*scale)//L
    assert lo==hi
    return 1 if lo%2==0 else -1

def run():
    scale=pow(99,5040+24)
    L,U=interval_pi(scale)
    assert 0<L<U
    expected={9:[1,-1,1,-1,1,1,-1],99:[-1,-1,1,1,-1,1,-1]}
    for base in (9,99):
        for n in range(1,8):
            k=factorial(n)
            sign=certified_sin_sign(base,k,scale,L,U)
            assert sign==expected[base][n-1],(base,n,sign)
            d=digit_alpha(base,k+1,scale,L,U)
            center=(base-1)//2
            if d!=center:
                assert sign==(1 if d<center else -1)
    assert digit_alpha(9,7,scale,L,U)==4
    assert digit_alpha(9,8,scale,L,U)==1
    d=digit_alpha(99,5041,scale,L,U)
    assert d==51
    a,b=divmod(d,11)
    assert (a-4,b-5)==(0,2)
    for d in range(99):
        a,b=divmod(d,11)
        assert d-49==11*(a-4)+(b-5)
        assert (98-d)-49==-(d-49)
    print('PASS: exact Machin intervals and fourteen factorial base-9/base-99 signs')
    print('PASS: base-9 neutral continuation and base-99 7! signed fibre (0,+2)')
    print('LIMIT: 9999! phase remains unresolved')

if __name__=='__main__':
    run()
