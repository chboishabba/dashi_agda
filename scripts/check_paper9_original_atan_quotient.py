#!/usr/bin/env python3
"""Exact regression of source Bishop atan finite quotient and second defect.

Grounded integer/rational algebra; NOT native Agda checking or
Bishop compact-uniform all-index bound.
"""
from fractions import Fraction as F
from math import factorial
import json


def Q(x,h,m):
    y=F(0)
    for j in range(m): y=y*(x+h)+x**j
    return y


def S(x,h,m):
    y=F(0)
    for j in range(m): y=y*(x+h)+Q(x,F(0),j)
    return y


def A(x,n):
    return sum((F((-1)**k,2*k+1)*x**(2*k+1) for k in range(n)),F(0))


def D(x,n):
    return sum((F((-1)**k)*x**(2*k) for k in range(n)),F(0))


def finite_Q(x,h,n):
    return sum((F((-1)**k,2*k+1)*Q(x,h,2*k+1) for k in range(n)),F(0))


def finite_S(x,h,n):
    return sum((F((-1)**k,2*k+1)*S(x,h,2*k+1) for k in range(n)),F(0))


def main():
    points=[(F(0),F(0)),(F(1,5),F(0)),(F(1,239),F(0)),(F(-1,5),F(1,239)),
      (F(1,5),F(-1,239)),(F(1,3),F(1,6)),(F(-1,2),F(1,5)),(F(1,2),F(-1,239))]
    count=0
    for x,h in points:
      assert abs(x)<=F(1,2) and abs(x+h)<=F(1,2)
      for n in range(0,33):
        q=finite_Q(x,h,n);s=finite_S(x,h,n)
        assert A(x+h,n)-A(x,n)==h*q
        assert q==D(x,n)+h*s
        assert finite_Q(x,F(0),n)==D(x,n)
        # Reference bound target: not a native proof of uniformity.
        assert abs(s)<=F(8,9)
        count+=4
    # Single-term all N tests of source-power exact factorisation.
    for x,h in points:
      for m in range(0,65):
        assert (x+h)**m-x**m==h*Q(x,h,m)
        assert Q(x,h,m)==Q(x,F(0),m)+h*S(x,h,m)
        count+=2
    a=F(1,5)
    assert A(a,3)!=sum((F(1,2*k+1)*a**(2*k+1) for k in range(3)),F(0))
    assert A(a,3)!=sum((F((-1)**k)*a**(2*k+1) for k in range(3)),F(0))
    assert A(a,3)!=A(F(1,239),3)
    print(json.dumps({'exact_identities_passed':count,'finite_precision_terms_max':32,
      'power_degree_max':64,'original_machin_points_tested':2,'uniform_second_defect_sample_bound':'8/9',
      'negative_controls_rejected':3,'all_index_bishop_bound_proved':False,'native_agda_checked':False},sort_keys=True))

if __name__=='__main__':main()
