#!/usr/bin/env python3
"""Exact natural-number slack certificate for the Machin 8/9 budget.

Checks the original positive-slack recurrence against the original
half-radius second quotient rational stage and the closed formula.
No Bishop/Agda kernel claim.
"""
import argparse
import json
from fractions import Fraction as F

def check(limit):
    power,slack,zero,second,budget=1,0,F(0),F(0),F(0)
    count=0
    for n in range(limit+1):
        assert power == 4**n
        assert power == 3*n+1+slack
        assert 0 <= slack <= power
        target=F(8*slack,9*power)
        assert target == budget
        assert target == F(8,9)*(1-F(3*n+1,power))
        assert target <= F(8,9)
        count+=6
        # A_n = source half-radius second quotient coefficient sum:
        # the next term for index n is qSecond(2*n+1)/(2*n+1)
        power2=1
        q0=q2=F(0)
        for m in range(2*n+1):
            q0,q2=q0*F(1,2)+F(1,2)**m,q2*F(1,2)+q0
            power2*=2
        atom=q2/F(2*n+1)
        assert atom==F(2*n,4**n)
        assert target+atom==F(8*(4*slack+9*n),9*(4*power))
        count+=2
        budget+=atom
        power,slack=4*power,4*slack+9*n
    # Mutations: both sign and 9*n coefficient essential.
    n,p,s=7,4**7,4**7-(3*7+1)
    assert 4*s+8*n != 4*p-(3*(n+1)+1)
    assert 4*s-9*n != 4*p-(3*(n+1)+1)
    return {"stages":limit+1,"identities":count,"mutants_rejected":2,
            "last_budget":str(budget),"Bishop_kernel_checked":False}

if __name__=="__main__":
    arg=argparse.ArgumentParser()
    arg.add_argument("--stages",type=int,default=120)
    a=arg.parse_args()
    assert 0 <= a.stages <= 1024
    print(json.dumps(check(a.stages),sort_keys=True))
