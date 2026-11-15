#!/usr/bin/env python3
"""Constructive compatible 2-adic square approximations for E:y²=x³-x.

At x=39, RHS=16*3705 and 3705≡1 (mod 8). Build root approximants
r_n²≡3705 (mod 2^n) with r_(n+1)≡r_n (mod 2^(n-1)).
For n>=3, choose b=((3705-r_n²)/2^n) mod 2 and
r_(n+1)=r_n+b*2^(n-1). The last square term 2^(2n-2)
is divisible by 2^(n+1), and odd r_n makes this a valid Hensel lift.
The sequence is 2-adically Cauchy and its limit r has r²=3705;
(39,4*r) is therefore a genuine E(Q2) point by Z2 completeness.

Finite checks are NOT an Agda construction of Q2/H1/Selmer.
"""
import json
VALUE = 3705

def trace(precision=512):
    assert precision>=4 and VALUE%8==1
    r=1
    result=[]
    for n in range(3,precision):
        two=1<<n
        assert (r*r-VALUE)%two==0
        assert r%2==1
        b=((VALUE-r*r)//two)&1
        next_r=r+(b<<(n-1))
        assert (next_r*next_r-VALUE)%(two*2)==0
        assert (next_r-r)%(1<<(n-1))==0
        if n in (3,4,5,6,8,16,32,64,128,256):
            result.append({"n":n,"residue":str(r),"next_bit":b})
        r=next_r
    return {"scheme":"bsd-Q2-coherent-hensel-v1",
            "curve":"y^2=x^3-x","x":39,
            "rhs":39*38*40,"unit":VALUE,
            "unit_mod8":VALUE%8,
            "precision":precision,
            "last_residue_hex":hex(r),
            "checkpoints":result,
            "result":"PASS","Q2_analytic_Hensel_argument":True,
            "Agda_Q2_H1_constructor":False,
            "Selmer_Sha_complete":False}

if __name__=="__main__":
    print(json.dumps(trace(),indent=2))
