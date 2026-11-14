#!/usr/bin/env python3
"""R445: exact sharp finite density-ratio/TV theorem stress test.

For same finite carrier, Q a positive probability and s=wP/wQ in [m,M],
Z=E_Q[s], TV(P,Q)=E_Q[(s-Z)_+]/Z, and the chord bound gives
TV <= (Z-m)*(M-Z)/(Z*(M-m)) <= (sqrt(M)-sqrt(m))/(sqrt(M)+sqrt(m)).
For s=e^{-Delta S} this is tanh(osc(Delta S)/4).

The unproved Yang--Mills source lemma is a *uniform* original Wilson
effective/target action-oscillation or TV bound. Generic finite density
algebra does not establish it; the tensor negative control proves why.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb
import json

def tv(P,R):
    assert len(P)==len(R) and sum(P)==sum(R)==1
    return sum((abs(p-q) for p,q in zip(P,R)), Q(0))/2

def finite_ratio_test(s,base):
    assert all(x>0 for x in s) and all(x>=0 for x in base)
    assert sum(base)==1
    z=sum((x*q for x,q in zip(s,base)),Q(0))
    m,M=min(s),max(s)
    P=[q*x/z for q,x in zip(base,s)]
    d=tv(P,base)
    chord=Q(0) if M==m else (M-z)*(z-m)/(z*(M-m))
    assert d<=chord and chord>=0
    # Avoid all floating-point square roots:
    # (M+m-(M-m)*d)^2 >= 4*m*M is the equivalent sharp inequality.
    q=M+m-(M-m)*d
    assert q>=0 and q*q>=4*m*M
    return d,chord

def tensor_tv(n):
    P0,P1=Q(1,5),Q(4,5)
    Q0,Q1=Q(4,5),Q(1,5)
    return sum((Q(comb(n,k),2)*abs(P0**k*P1**(n-k)-Q0**k*Q1**(n-k))
               for k in range(n+1)),Q(0))

def check():
    m,M=Q(1,4),Q(4)
    d,chord=finite_ratio_test([m,M],[Q(4,5),Q(1,5)])
    assert d==chord==Q(3,5)
    count=1
    for n in range(2,6):
        for s in product((Q(1,4),Q(1),Q(4)),repeat=n):
            finite_ratio_test(s,[Q(1,n)]*n)
            count+=1
    sizes=(1,2,4,6,8,12,16)
    vals=[tensor_tv(n) for n in sizes]
    assert vals[-1]>Q(99,100)
    assert all(x<=y for x,y in zip(vals,vals[1:]))
    return {"schema":"ym-r445-sharp-tv-v1","result":"PASS",
            "exact_cases":count,"sharp_two_state_ratio_D":str(d),
            "tensor_volume_negative_control":
                {str(n):str(v) for n,v in zip(sizes,vals)},
            "source_Wilson_uniform_bound":False,"agda_kernel_checked":False}

if __name__ == "__main__":
    print(json.dumps(check(),indent=2))
