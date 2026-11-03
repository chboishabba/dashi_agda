#!/usr/bin/env python3
"""Exact exhaustive finite-K centering-factor audit (Dust Eq. 2 affine case).
Original method: Dahal, Mandal, Gulbahar, Vegesna (2026).
DASHI owns finite enumerative check. This is not Gaussian sampling nor GPU reproduction.
"""
from fractions import Fraction as F
from itertools import product
import json

def sample_covariance_factor(draws):
    k = len(draws)
    mean = sum(draws,F(0))/k
    return sum(((a-mean)*a for a in draws),F(0))/k

def main():
    result={}
    for k in range(1,9):
        population=product((F(-1),F(1)),repeat=k)
        total=sum((sample_covariance_factor(draws) for draws in population),F(0))
        observed=total/(2**k)
        expected=F(k-1,k)
        assert observed==expected,(k,observed,expected)
        result[str(k)]={"finite_K_factor":str(observed),"cases":2**k,
                        "expected":str(expected)}
    print(json.dumps(result,indent=2))
if __name__=="__main__":
    main()
