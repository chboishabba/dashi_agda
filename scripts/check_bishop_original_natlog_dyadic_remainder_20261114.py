#!/usr/bin/env python3
"""Exact rational negative-log dyadic remainder on the ORIGINAL index.

For ell_N(x)=sum_(j=1)^N x^j/j and z=x+(1-x)y:
 d/dt[ell_N(x+(1-x)t)-ell_N(t)-ell_N(x)]
   = (t^N-(x+(1-x)t)^N)/(1-t)
   = -x*sum_(j=0)^(N-1)(x+(1-x)t)^(N-1-j)*t^j.
For 0<=x,y<1:
  0<=ell_N(x)+ell_N(y)-ell_N(z)<=y*z^N/(1-y).
Select x=1/2, y=(m-1)/m, z=(2m-1)/(2m):
  0<=L_N(2)+L_N(m)-L_N(2m)<=(m-1)*z^N.
This supplies explicit geometric quantitative input for the original
negative-log Bishop series, NOT a checked Agda setoid limit transport.
"""
from fractions import Fraction as F
from math import comb
import json

def partial(x,n):return sum((x**k/F(k) for k in range(1,n+1)),F(0))
def derivative(x,n):return sum((x**k for k in range(n)),F(0))
def integral_polynomial(x,y,n):
    return x*sum((F(comb(n-1-j,h))*x**(n-1-j-h)*
      (1-x)**h*y**(h+j+1)/F(h+j+1)
      for j in range(n) for h in range(n-j)),F(0))
def cutoff(m,eps):
    z=F(2*m-1,2*m)
    term=F(m-1)
    if term<eps:return 1
    n=0
    while term>=eps:
        n+=1
        term*=z
    assert F(m-1)*z**n<eps
    return n
def check():
    derivatives=0; polynomials=0; bounds=0
    for n in range(1,16):
        for x in (F(1,2),F(1,4),F(2,3)):
            for t in (F(0),F(1,5),F(1,2),F(7,8)):
                z=x+(1-x)*t
                lhs=(1-x)*derivative(z,n)-derivative(t,n)
                rhs=(t**n-z**n)/(1-t)
                poly=-x*sum((z**(n-1-j)*t**j for j in range(n)),F(0))
                assert lhs==rhs==poly
                derivatives+=1
    for m in range(1,21):
        x,y=F(1,2),F(m-1,m)
        z=x+(1-x)*y
        assert z==F(2*m-1,2*m)
        for n in range(1,21):
            diff=partial(x,n)+partial(y,n)-partial(z,n)
            assert 0<=diff<=F(m-1)*z**n
            bounds+=1
            if n<=10:
                assert diff==integral_polynomial(x,y,n)
                polynomials+=1
    cs={str(m):cutoff(m,F(1,100)) for m in (1,2,3,5,10,20)}
    assert cs=={'1':1,'2':17,'3':30,'5':57,'10':133,'20':299}
    return {'schema':'bishop-original-negative-log-dyadic-remainder-v1',
      'result':'PASS','exact_polynomial_derivative_cases':derivatives,
      'exact_rational_polynomial_integral_cases':polynomials,
      'exact_rational_remainder_bound_cases':bounds,
      'source_index':'L(n)=sum_(j>=1)(n/(n+1))^j/j',
      'physical_equation':'L(2m)=L(2)+L(m); Nat indices 2m-1,1,m-1',
      'finite_bound':'0<=LN(2)+LN(m)-LN(2m)<=(m-1)*((2m-1)/(2m))^N',
      'rational_cutoff_eps_1_over_100':cs,
      'original_Bishop_setoid_limit_transport_proved':False,
      'originalDyadicNatLogLaw_agda_kernel_checked':False}
if __name__=='__main__':print(json.dumps(check(),indent=2))
