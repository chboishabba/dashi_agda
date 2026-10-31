#!/usr/bin/env python3
"""Certified sin(99**m) by compressed modular phase and exact real-error control.

The Machin rational interval [L,U] encloses trigonometric pi (subject to
the historical Machin identity; DASHI Bishop branch owner is separate).
Let alpha=(L+U)/2=a/b and delta=(U-L)/2.
Compute r=(b*99**m) mod (2*a), then choose -a<=r<=a.
There exists an integer winding q such that
  99**m = r/b + 2*q*alpha
and |q| <= b*99**m/(2*a)+1. Therefore
  |sin(99**m)-sin(r/b)| <= (b*99**m/a+2)*delta
by the Lipschitz property of sine.
Use an exact rational Taylor enclosure about r/b.
IMPORTANT: modular arithmetic alone does NOT bound this drift; if the
error budget fails, return INCONCLUSIVE. This is not a terminal result
for sin(99**(9999!)).

At fixed Machin precision, a capped integer-power comparison rejects
unfeasible exponents without ever expanding 99**m.
"""
from fractions import Fraction as Q
from math import factorial
import argparse

def arctan_interval(d,k):
    assert d>1 and k>=1
    s=sum((Q((-1)**j,(2*j+1)*d**(2*j+1)) for j in range(k)),Q(0))
    t=Q(1,(2*k+1)*d**(2*k+1))
    return (s,s+t) if k%2==0 else (s-t,s)

def pi_interval(k):
    l5,u5=arctan_interval(5,k)
    l239,u239=arctan_interval(239,k)
    return 16*l5-4*u239,16*u5-4*l239

def capped_power(base,exp,cap):
    """Returns min(base**exp,cap+1), O(log exp) bounded-size products."""
    result,power=1,min(base,cap+1)
    while exp:
        if exp&1: result=min(cap+1,result*power)
        exp//=2
        if exp: power=min(cap+1,power*power)
    return result

def sine_interval(x,k):
    assert k>=0
    s=sum((Q((-1)**j)*x**(2*j+1)/factorial(2*j+1)
           for j in range(k+1)),Q(0))
    radius=abs(x)**(2*k+3)/factorial(2*k+3)
    return s-radius,s+radius

def certify(m,pi_terms=32,sine_terms=24):
    assert m>=0
    L,U=pi_interval(pi_terms)
    alpha=(L+U)/2
    delta=(U-L)/2
    a,b=alpha.numerator,alpha.denominator
    assert 0<L<=alpha<=U and delta>0 and a>0
    # Sufficient to guarantee global drift < 1/8; else no potentially
    # expensive actual 99**m is constructed.
    budget=Q(1,8)-2*delta
    if budget<=0:
        return {"status":"INCONCLUSIVE","reason":"pi interval too wide"}
    cap=int((budget*a)/(b*delta))
    value=capped_power(99,m,cap)
    if value>cap:
        return {"status":"INCONCLUSIVE","reason":
                "certified real-phase drift exceeds preflight budget",
                "m_bits":m.bit_length(),"pi_terms":pi_terms}
    N=value
    residue=(b*pow(99,m,2*a))%(2*a)
    if residue>a: residue-=2*a
    phase=Q(residue,b)
    drift=(Q(b*N,a)+2)*delta
    assert drift<Q(1,8)
    low,high=sine_interval(phase,sine_terms)
    low-=drift; high+=drift
    sign=1 if low>0 else (-1 if high<0 else 0)
    return {"status":"CERTIFIED" if sign else "INCONCLUSIVE",
            "sign":sign,"winding_surrogate":str(phase),
            "sine_lower":str(low),"sine_upper":str(high),
            "phase_error_bound":str(drift),
            "m_bits":m.bit_length()}

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--m",type=int,default=8)
    parser.add_argument("--pi-terms",type=int,default=32)
    parser.add_argument("--sine-terms",type=int,default=24)
    args=parser.parse_args()
    result=certify(args.m,args.pi_terms,args.sine_terms)
    for name,value in result.items(): print(f"{name}: {value}")
    if result["status"]!="CERTIFIED": raise SystemExit(2)
