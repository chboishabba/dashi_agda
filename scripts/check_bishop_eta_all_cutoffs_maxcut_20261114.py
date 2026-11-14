#!/usr/bin/env python3
"""Exact arithmetic + all-cutoff complex diagnostics for Bishop eta.

Original Nat index j denotes positive integer j+1:
  a_s(j)=expC(-s*L(j)), L(j) intended log(j+1).
Paired tails alone do NOT control odd final partial-sum cutoffs.

For 1<=N<=M, Re(s)>=delta>0 and |s|<=R:
  |sum_(n=N)^M (-1)^(n-1)n^-s| <= (1+R/delta)*N^-delta.
The source Bishop Nat-log, exp, derivative, FTC and SeriesOf
transport are separate open gates. Tests do not replace Agda kernel.
"""
from fractions import Fraction as F
from itertools import product
import math, cmath, json

def first_cutoff(delta:F, coeff:F, eps:F):
    """Least N>=1 s.t. coeff*N^(-delta)<=eps, exact integer powers."""
    assert delta>0 and coeff>0 and eps>0
    p,q=delta.numerator,delta.denominator
    r=coeff/eps
    def fits(n):return n**p*r.denominator**q>=r.numerator**q
    high=1
    while not fits(high):high*=2
    low=0
    while high-low>1:
        m=(low+high)//2
        if fits(m):high=m
        else:low=m
    assert fits(high) and (high==1 or not fits(high-1))
    return high

def finite_abel(a):
    lhs=sum(((-1)**j*a[j] for j in range(len(a))),F(0))
    if not a:return lhs,F(0)
    partial,rhs=0,F(0)
    for j in range(len(a)-1):
        partial+=(-1)**j
        rhs+=partial*(a[j]-a[j+1])
    partial+=(-1)**(len(a)-1)
    return lhs,rhs+partial*a[-1]

def real_block(s,n,m):
    return sum((F((-1)**(k-1),k**s) for k in range(n,m+1)),F(0))

def check():
    exact_abel=0
    for n in range(8):
        for a in product((F(-5,3),F(0),F(1,7),F(3,2)),repeat=n):
            assert finite_abel(a)[0]==finite_abel(a)[1]
            exact_abel+=1
    real_all=0; real_pairs=0
    for s in (1,2,3,4):
        for N in range(1,30):
            for M in range(N,N+17):
                assert abs(real_block(s,N,M))<=F(2,N**s)
                real_all+=1
        for start in range(1,19):
            for stop in range(start+1,start+9):
                assert abs(real_block(s,2*start+1,2*stop))<=F(1,(2*start)**s)
                real_pairs+=1
    delta,C,eps=F(1,2),F(9),F(1,10)
    weak=first_cutoff(delta,C,eps)
    strict=first_cutoff(delta,C,eps/2)
    assert (weak,strict)==(8100,32400)
    complex_checks=0; max_ratio=0.
    for s in (complex(.5,0),complex(.5,3),complex(.75,1.25),
              complex(1,8),complex(2.25,1.2)):
        for n in (1,2,3,7,13,51,101):
            for length in (1,2,3,4,7,20,80):
                block=sum((-1)**(k-1)*cmath.exp(-s*math.log(k))
                          for k in range(n,n+length))
                bound=(1+abs(s)/s.real)*n**(-s.real)
                assert abs(block)<=bound*(1+2e-11)
                max_ratio=max(max_ratio,abs(block)/bound)
                complex_checks+=1
    return {'schema':'bishop-eta-original-indexed-all-cutoffs-maxcut-v1',
      'result':'PASS','source_index':'a_s(j)=expC(-s*L(j)); L(j) is intended log(j+1)',
      'exact_rational_finite_abel_cases':exact_abel,
      'exact_real_arbitrary_endpoint_blocks':real_all,
      'exact_real_complete_pair_tails':real_pairs,
      'complex_numeric_all_cutoff_checks':complex_checks,
      'max_numeric_ratio_to_bound':max_ratio,
      'all_endpoints_bound':'(1+R/delta)*N^(-delta)',
      'pairs_only_bound':'(R/delta)*(2*M)^(-delta)',
      'exact_constructive_cutoff':{'delta':'1/2','C':'9','eps':'1/10',
        'N_weak':weak,'N_strict_via_half_epsilon':strict},
      'original_nat_log_dyadic_law_agda_proved':False,
      'bishop_derivative_FTC_agda_proved':False,
      'original_round11_compact_uniform_kernel_receipt':False}
if __name__=='__main__':print(json.dumps(check(),indent=2))
