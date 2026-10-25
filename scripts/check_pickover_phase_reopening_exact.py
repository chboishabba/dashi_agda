#!/usr/bin/env python3
"""Exact Machin-pi based signed phase tail check. No float trigonometry.
Certified finite cases only; 9999! sign NOT claimed.
"""
from math import factorial
from fractions import Fraction

def pi_window(scale):
    def atan(q):
        p=q;j=0;sgn=1;acc=0
        while True:
            t=scale//((2*j+1)*p)
            if not t:return acc,j
            acc+=sgn*t
            sgn=-sgn;j+=1;p*=q*q
    a,na=atan(5);b,nb=atan(239)
    c=16*a-4*b;err=16*(na+2)+4*(nb+2)
    return c-err,c+err

def first_tail(base,k,scale,lower,upper,count=6):
    lo=Fraction(base**k*scale,2*upper)
    hi=Fraction(base**k*scale,2*lower)
    qlo=lo.numerator//lo.denominator
    qhi=hi.numerator//hi.denominator
    if qlo!=qhi:raise AssertionError('insufficient precision at shift')
    lo-=qlo;hi-=qhi
    digits=[]
    for _ in range(count):
        lo*=base;hi*=base
        qlo=lo.numerator//lo.denominator
        qhi=hi.numerator//hi.denominator
        if qlo!=qhi:raise AssertionError('insufficient precision at digit')
        digits.append(qlo)
        lo-=qlo;hi-=qhi
    return digits

def main():
    scale=99**(5040+35)
    lo,hi=pi_window(scale)
    expect=[-1,-1,1,1,-1,1,-1]
    for n in range(1,8):
        k=factorial(n)
        digits=first_tail(99,k,scale,lo,hi)
        first=next((d for d in digits if d!=49),None)
        assert first is not None
        signed=1 if first<49 else -1
        qlo=(99**k*scale)//hi;qhi=(99**k*scale)//lo
        assert qlo==qhi and signed==(1 if qlo%2==0 else -1)
        assert signed==expect[n-1]
        a,b=divmod(digits[0],11)
        assert digits[0]-49==11*(a-4)+(b-5)
        print(n,k,digits[0],a-4,b-5,signed)
    for d in range(99):
        a,b=divmod(d,11)
        assert 11*(a-4)+(b-5)==d-49
        A,B=divmod(98-d,11)
        assert (A-4,B-5)==(4-a,5-b)
    print('PASS: seven factorial signs, 9x11 carry codec and antipode')
    print('OPEN: real-phase tail at position 9999!+1')
if __name__=='__main__': main()
