#!/usr/bin/env python3
"""Fast sine via angle-free fixed-point complex powers, rigorously bounded.
Classic de Moivre / exponentiation by squaring; DASHI: Pickover cost audit.
No repeated trigonometric reduction, no floating-point arithmetic.
For moderate integer N, z=e^i is seeded via certified alternating
Taylor enclosures for sin(1),cos(1), then z^N is computed in O(log N)
complex squarings using fixed-point roundoff plus propagated error.
"""
from fractions import Fraction
from math import factorial

def round_fixed(q,S):
    return (q.numerator*S*2//q.denominator+1)//2

def ceil_fraction(f):
    return -(-f.numerator//f.denominator)

def seed(S,terms):
    c=sum(((-1)**k*Fraction(1,factorial(2*k)) for k in range(terms)),Fraction())
    s=sum(((-1)**k*Fraction(1,factorial(2*k+1)) for k in range(terms)),Fraction())
    a,b=round_fixed(c,S),round_fixed(s,S)
    # alternating tails of each coordinate; plus fixed rounding <=1/S
    error=Fraction(1,factorial(2*terms))+Fraction(1,factorial(2*terms+1))+Fraction(2,S)
    return (a,b),ceil_fraction(error*S)

def product(x,y,S):
    a,b=x;c,d=y
    return ((a*c-b*d+S//2)//S,(a*d+b*c+S//2)//S)

def power_certified(N,digits):
    S=10**digits
    z,eps=seed(S,max(12,digits//2+4))
    # Each complex multiply error <= sqrt(2)/S <2/S.
    # Use conservative norm bound |z_approx|<= 1+eps, and
    # sequential recurrences for exponent bit scan.
    result=(S,0);err=0
    base=z;base_err=eps
    e=N
    ops=0
    while e:
        if e&1:
            result=product(result,base,S)
            err=err+base_err+(err*base_err+S-1)//S+2
            ops+=1
            if err >= S: return None,ops,err
        e>>=1
        if e:
            base=product(base,base,S)
            base_err=2*base_err+(base_err*base_err+S-1)//S+2
            ops+=1
            if base_err >= S: return None,ops,base_err
    if abs(result[1])<=err:return None,ops,err
    return (1 if result[1]>0 else -1),ops,err

def main():
    for base in (10,99):
        for k in (1,2,6,24,120):
            N=pow(base,k)
            found=None
            for digits in (20,50,100,200,350,500):
                sign,ops,err=power_certified(N,digits)
                if sign is not None:
                    found=(digits,sign,ops)
                    break
            assert found is not None,(base,k)
            print('base',base,'exponent',k,'decimal_precision',found[0],'certified_sign',found[1],'complex_multiplies',found[2])
    print('PASS rigorous fixed-point complex-power sine-sign certificates')
    print('NOTE operand bit width scales with log N; this alone does not solve E=9999!')
if __name__=='__main__':main()
