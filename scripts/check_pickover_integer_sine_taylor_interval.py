#!/usr/bin/env python3
"""Exact rational sine-sign certificate via Taylor remainder.

For a POSITIVE integer n, S_m=sum_{k=0}^m (-1)^k n^(2k+1)/(2k+1)!,
R_m=n^(2m+3)/(2m+3)!, and |sin(n)-S_m|<=R_m by Taylor's
theorem (the even next coefficient vanishes and every real derivative
of sine has absolute value <=1). If S_m-R_m>0 or S_m+R_m<0,
this gives an unconditional exact rational sign certificate.

The algorithm is total for every n>0 in classical mathematics:
sin(n)=0 implies n is an integer multiple of pi, contrary to pi's
irrationality. This does NOT make it computationally feasible for
n=99^(9999!). No fake large-n result is returned.

The printed certificate contains exact integer numerators/denominators,
and is independently checkable with the above Taylor bound.
"""
from fractions import Fraction
from sys import argv

def decide(n, max_terms):
    if n<=0: raise ValueError("positive integer argument required")
    term=Fraction(n,1)
    summation=Fraction(0)
    for k in range(max_terms):
        summation += term
        # next term magnitude is rigorous Taylor remainder for degree 2k+2
        remainder=abs(term)*n*n/Fraction((2*k+2)*(2*k+3),1)
        lo,hi=summation-remainder,summation+remainder
        if lo>0: return (1,k,lo,hi)
        if hi<0: return (-1,k,lo,hi)
        term=-term*n*n/Fraction((2*k+2)*(2*k+3),1)
    return None

def main():
    n=int(argv[1]) if len(argv)>1 else 1
    budget=int(argv[2]) if len(argv)>2 else 64
    result=decide(n,budget)
    if result is None:
        print("INCONCLUSIVE: insufficient exact Taylor terms")
        raise SystemExit(2)
    sign,k,lo,hi=result
    assert lo>0 if sign==1 else hi<0
    print(f"CERTIFIED sign(sin({n}))={sign} terms={k+1}")
    print(f"exact rational enclosure: [{lo}, {hi}]")
if __name__=="__main__":main()
