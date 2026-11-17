#!/usr/bin/env python3
"""One exact integer (P,Q,B,T) finite hypergeometric evaluator.

This is an arithmetic reference and negative control, not yet an
Agda proof or a claim of equal Bishop-series limits.
Classical sources: Machin; Euler; Apéry; Bishop/Bridges; Murray/Csimma.
"""
from fractions import Fraction as F
from math import comb, isqrt
from statistics import median
from time import perf_counter

def merge(left, right):
    p,q,b,t = left
    P,Q,B,T = right
    return (p*P, q*Q, b*B, t*Q*B + p*b*T)

def split(seq):
    if not seq:
        return (1,1,1,0)
    if len(seq) == 1:
        a,b,p,q = seq[0]
        assert b>0 and q>0
        return (p,q,b,a*p)
    m = len(seq)//2
    return merge(split(seq[:m]),split(seq[m:]))

def direct(seq):
    product, acc = F(1), F(0)
    for a,b,p,q in seq:
        product *= F(p,q)
        acc += F(a,b)*product
    return acc

FAMILIES = {
    "atan(1/5)": lambda k: ((-1)**k,2*k+1,1,5 if k==0 else 25),
    "exp(1)": lambda k: (1,1,1,1 if k==0 else k),
    "ln(2)": lambda k: (2,3*(2*k+1),1,1 if k==0 else 9),
    # IMPORTANT: previous suggested 4*k*(2*k-1) denominator
    # is incorrect by a factor of 2 for the inverse binomial ratio.
    "zeta(3)": lambda k: (5*(-1)**(k-1),2*k**3,
                          1 if k==1 else k*k,
                          2 if k==1 else 2*k*(2*k-1))
}

def pell_bracket(D,p,q,n):
    assert D>=2 and p*p-D*q*q==1
    for _ in range(n):
        p,q = p*p+D*q*q,2*p*q
    assert p*p-D*q*q==1
    lower, upper = F(D*q,p),F(p,q)
    assert upper-lower==F(1,p*q)
    assert lower*lower < D < upper*upper
    return lower,upper

def dyadic_sqrt_bracket(D,bits):
    z = isqrt(D<<(2*bits))
    lo,hi=F(z,1<<bits),F(z+1,1<<bits)
    assert lo*lo<=D<=hi*hi
    return lo,hi

def tests():
    for name,f in FAMILIES.items():
        start = 1 if name=="zeta(3)" else 0
        for a in range(start,start+6):
            for n in range(1,10):
                seq=[f(k) for k in range(a,a+n)]
                p,q,b,t=split(seq)
                assert F(t,q*b)==direct(seq),(name,a,n)
    for n in range(1,25):
        seq=[FAMILIES["zeta(3)"](k) for k in range(1,n+1)]
        p,q,b,t=split(seq)
        expected=sum((F(5*(-1)**(k-1),2*k**3*comb(2*k,k))
                      for k in range(1,n+1)), F(0))
        assert F(t,q*b)==expected
    for D,p,q in ((2,3,2),(3,2,1),(6,5,2)):
        for n in range(10):
            pell_bracket(D,p,q,n)
    print("PASS exact 4-family P/Q/B/T finite sums and Pell-square rational bounds")

def benchmark():
    tests()
    for D,p,q in ((2,3,2),(3,2,1),(6,5,2)):
        for n in (5,7,9):
            lo,hi = pell_bracket(D,p,q,n)
            bits=max(1,((hi-lo).denominator//(hi-lo).numerator).bit_length())
            timing=[]
            for f in (lambda:pell_bracket(D,p,q,n),
                      lambda:dyadic_sqrt_bracket(D,bits)):
                samples=[]
                for _ in range(9):
                    t=perf_counter();f();samples.append((perf_counter()-t)*1000)
                timing.append(round(median(samples),5))
            print(dict(D=D,n=n,certified_bits_at_least=bits-1,
                       pell_ms=timing[0],integer_isqrt_ms=timing[1]))

if __name__=="__main__":
    benchmark()
