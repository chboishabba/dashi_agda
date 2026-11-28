#!/usr/bin/env python3
"""BR82: exact BR37 glancing ray and quantitative derivative-loss frontier.

The ORIGINAL BR37 physical D/E frozen inverse has chart factors
M^4 (metric) and M^2 (subsidiary) with M=12Q,
Q=max(1,max(|s|,|xi|)/|ell|) and ell²=s²+|xi|².
Along a genuinely damped glancing ray:
  s=sigma+i omega, xi=omega, sigma>0,
  ell²=sigma²+2i sigma omega,
  |ell|^4=sigma^4+4 sigma² omega².
Define r=omega/sigma. For r>=3, Q_spatial=omega/|ell|>1:
  r²/5 <= Q_spatial^4=r^4/(1+4r²) <= r²/4,
  r/sqrt5 <= Q_spatial²=r²/sqrt(1+4r²) <= r/2.
The physical time covector may be even larger by a bounded factor;
the spatial lower bound alone proves no frequency-uniform estimate
from BR37's current *particular conjugation bound*.

At fixed damping sigma, M^4 is quadratic in tangential frequency
along this ray (two derivative powers), while M² is linear
(one derivative power). This is NOT a sharp global Kreiss theorem;
the original symbols may possess a better estimate in a source
adapted symmetrizer. A frequency-independent BR37 bound cannot
be claimed from its present M^4/M^2 argument.

No floating thresholds; all polynomial comparisons exact rational.
"""
import argparse
import sympy as s
from fractions import Fraction as F

def ratio(r):
    r=F(r)
    q4=r**4/(1+4*r*r)
    return r,q4

def algebra():
    r=s.symbols('r',positive=True)
    q4=r**4/(1+4*r*r)
    assert s.factor(q4-r*r/5)==r*r*(r*r-1)/(5*(1+4*r*r))
    assert s.factor(r*r/4-q4)==r*r/(4*(1+4*r*r))
    # Q_spatial>=1 for r>=3, so the BR37 max selects this ray.
    assert ratio(3)[1]>1
    print('PASS BR82 exact damped glancing Q^4 sandwich and no characteristic root division')

def growth():
    for r in (F(3),F(4),F(10),F(100),F(1000)):
        rr,q4=ratio(r)
        assert rr*rr/5<=q4<=rr*rr/4
        assert q4>1
        M4=12**4*q4
        M2=12**2*s.sqrt(q4)
        assert M4>0 and M2>0
        # The inverse multiplier growth can be paid by weighted
        # tangential norms of different orders in this source ray.
    print('PASS BR82 glancing 2/1 tangential derivative power lower/upper asymptotic')

def refusal():
    for C in (F(1),F(10),F(1000)):
        r=F(4)*(C+1)
        _,q4=ratio(r)
        assert q4>C
    # This is a refusal of the CURRENT upper-bound proof, not a
    # mathematical theorem that no improved uniform symmetrizer exists.
    print('PASS BR82 REFUSAL: BR37 particular M^4 chart cost is not uniformly bounded')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['algebra','growth','refusal'],default='algebra')
    a=p.parse_args()
    {'algebra':algebra,'growth':growth,'refusal':refusal}[a.part]()
