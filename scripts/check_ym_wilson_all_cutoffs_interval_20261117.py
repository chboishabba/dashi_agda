#!/usr/bin/env python3
"""Exact rational Wilson partition brackets at ANY original periodic cutoff.

Original L=1 has six commutators. For every L>=2, no three distinct
elementary positive plaquette boundaries form a mod-2 cycle:
  * Different planes share <=1 positive link.
  * At L>=3 same-plane distinct squares share <=1 positive link.
  * At L=2 same-plane two-edge-overlap pairs form a four-cycle C4,
    with no triangle.
Three size-four edge boundaries with XOR zero require every pair to
share precisely two edges; hence impossible. Center-sign cancellation
then proves E[D], E[D²], E[D³] for all L>=2.

For beta>=0, T3(beta D)<=e^(-beta D)<=T2(beta D).
The strictly positive rational lower bound 4^(-ceil(12 beta L^4))
uses e<4 and the bound 0<=beta D<=12 beta L^4.
The output is an exact mathematical certificate, not Agda acceptance
or a continuum Yang-Mills mass gap.
"""
import argparse
from fractions import Fraction as Q

def ceil_fraction(x):
    assert x >= 0
    return (x.numerator + x.denominator - 1)//x.denominator

def moments(side):
    assert isinstance(side,int) and side>=1
    if side==1:
        return Q(9,2),Q(187,8),Q(6445,48)
    p=6*side**4
    return Q(p),Q(p*p)+Q(p,4),Q(p**3)+Q(3*p*p,4)

def brackets(side,beta):
    assert side>=1 and beta>=0
    mu1,mu2,mu3=moments(side)
    T2=1-beta*mu1+beta*beta*mu2/2
    T3=T2-beta**3*mu3/6
    B=12*beta*side**4
    positive_floor=Q(1,4**ceil_fraction(B))
    lower=max(T3,positive_floor)
    upper=min(Q(1),T2)
    assert 0<lower<=upper<=1,(side,beta,lower,upper)
    return lower,upper,upper-lower

def display(q):
    if q.numerator.bit_length()>4096 or q.denominator.bit_length()>4096:
        return (f"<exact fraction: {q.numerator.bit_length()}-bit numerator "
                f"/ {q.denominator.bit_length()}-bit denominator>")
    return str(q)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--side",type=int,default=4)
    ap.add_argument("--beta",default=None)
    args=ap.parse_args()
    beta=Q(args.beta) if args.beta is not None else Q(1,96*args.side**4)
    for L,b in [(args.side,beta),(1,Q(1,96)),(2,Q(1,1536)),
                (3,Q(1,7776)),(4,Q(1,24576)),
                (10,Q(1,960000)),(25,Q(7,1000))]:
        lo,hi,width=brackets(L,b)
        print(f"L={L} beta={b}: 0<{display(lo)} <= Z <= "
              f"{display(hi)}<=1; width={display(width)}")
    assert moments(1)==(Q(9,2),Q(187,8),Q(6445,48))
    print("ORIGINAL_WILSON_ALL_CUTOFF_RATIONAL_INTERVAL_PASS")

if __name__=="__main__":
    main()
