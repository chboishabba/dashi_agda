#!/usr/bin/env python3
"""Exact factorial Cauchy identities for the native Bishop sine/cosine source.

Finite rational algebra only; selected original real-setoid coefficient
transport, Cauchy-product limit and trig-add kernel receipts remain OPEN.
"""
from fractions import Fraction as Q
from math import factorial
import json

def cos_coeff(x,y,n):
    cc=sum((Q((-1)**n,factorial(2*j)*factorial(2*(n-j)))*
        x**(2*j)*y**(2*(n-j)) for j in range(n+1)),Q(0))
    ss=sum((Q((-1)**(n-1),factorial(2*j+1)*factorial(2*(n-j)-1))*
        x**(2*j+1)*y**(2*(n-j)-1) for j in range(n)),Q(0))
    return cc-ss

def sin_coeff(x,y,n):
    sc=sum((Q((-1)**n,factorial(2*j+1)*factorial(2*(n-j)))*
        x**(2*j+1)*y**(2*(n-j)) for j in range(n+1)),Q(0))
    cs=sum((Q((-1)**n,factorial(2*j)*factorial(2*(n-j)+1))*
        x**(2*j)*y**(2*(n-j)+1) for j in range(n+1)),Q(0))
    return sc+cs

def even_tail_bound(R,N):
    r=R*R/Q((2*N+1)*(2*N+2))
    if r>=1:return None
    return R**(2*N)/Q(factorial(2*N))/(1-r)

def check():
    tests=0
    xs=(Q(0),Q(1),Q(-1),Q(1,3),Q(-7,5),Q(5,2))
    for x in xs:
        for y in xs:
            for n in range(13):
                assert cos_coeff(x,y,n)==Q((-1)**n,factorial(2*n))*(x+y)**(2*n)
                assert sin_coeff(x,y,n)==Q((-1)**n,factorial(2*n+1))*(x+y)**(2*n+1)
                tests+=2
    tails=0
    for R in (Q(1,4),Q(1),Q(2),Q(5,2)):
        for N in range(1,14):
            bound=even_tail_bound(R,N)
            if bound is None:continue
            for M in range(N,2*N+18):
                actual=sum((R**(2*k)/Q(factorial(2*k)) for k in range(N,M+1)),Q(0))
                assert actual<=bound
                tails+=1
    return {'schema':'bishop-original-trig-factorial-cauchy-finite-v1',
      'result':'PASS','rational_cos_sin_coefficient_cases':tests,
      'rational_even_tail_envelope_cases':tails,
      'tail_bound':'R^(2N)/(2N)!/(1-R^2/((2N+1)(2N+2)))',
      'original_configured_coefficient_weld':False,
      'original_Bishop_product_limit':False,
      'original_trig_addition_kernel':False}
if __name__=='__main__':print(json.dumps(check(),indent=2))
