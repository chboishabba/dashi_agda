#!/usr/bin/env python3
"""Exact rational majorant for the local exponential Koenigs limit.

Input analytic hypotheses (to formalize over Bishop complex):
  Log(p)=p, 1.37<|p|<1.38, |z-p|<=r<=0.1,
  |Log(z)-p| <= (4/5)|z-p|,
  |Log(p+t)-p-t/p| <= (311/1000)|t|^2.
Then for h_n=p^n(Log^n(z)-p),
  |h_{n+1}-h_n| <= (69/50)*(311/1000)*beta^n*r^2,
  beta=(69/50)*(4/5)^2=552/625<1,
  |chi-h_N| <= prefactor*beta^N*r^2.
All algebraic checks and reported bounds are exact Fraction calculations.
"""
from fractions import Fraction as F

LAM=F(69,50)
Q=F(4,5)
M=F(311,1000)
BETA=LAM*Q*Q
PREF=LAM*M/(1-BETA)

def upper(n: int, r: F) -> F:
    if n<0 or r<0 or r>F(1,10):
        raise ValueError('need n>=0 and 0<=r<=1/10')
    return PREF*BETA**n*r*r

def check():
    assert BETA==F(552,625) and BETA==F(8832,10000)
    assert PREF==F(21459,5840)
    assert (LAM*M)*sum(BETA**k for k in range(15)) == PREF*(1-BETA**15)
    for r in (F(1,10),F(1,1000)):
        for n in (0,10,40,80,200):
            tail=upper(n,r)
            assert tail>=0
            assert upper(n+1,r)==BETA*tail
            print('n=%d, |z-p|<=%s, bound<=%.12g' % (n,str(r),float(tail)))
    assert upper(200,F(1,10))<F(1,10**10)
    assert upper(80,F(1,1000))<F(1,10**9)
    print('PASS exact Fraction Koenigs geometric-tail identities')

if __name__=='__main__':
    check()
