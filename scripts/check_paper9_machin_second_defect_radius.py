#!/usr/bin/env python3
"""Exact finite checks for the ALL-N algebraic Machin second quotient radius.

The direct polynomial recurrence is the original Bishop LOG power spine.
Its coefficient formula gives an *algebraic all-N proof plan*:
T_m(x,y)=sum_{j=0}^{m-2}(j+1)*x^j*y^(m-2-j).
Thus |T_(2k+1)|/(2k+1)<=k*(1/2)^(2k-1) for |x|,|y|<=1/2.
The last all-N inequality on native Bishop order is NOT certified here.
"""
from fractions import Fraction as F
import sympy as s
import json

def qpoly(x,y,m):
    q=0
    for j in range(m): q+=x**j*y**(m-1-j)
    return q

def tpoly(x,y,m):
    return sum((j+1)*x**j*y**(m-2-j) for j in range(max(0,m-1)))

def budget(n):
    return sum((F(2*k,4**k) for k in range(n)),F(0))

def closed(n):
    return F(8,9)*(1-F(3*n+1,4**n))

def numerical_t(x,y,m):
    t=q=F(0)
    for j in range(m):
        t=y*t+(j*x**(j-1) if j else 0)
        q=y*q+x**j
    return t

def main():
    x,y=s.symbols('x y')
    q=t=s.Integer(0)
    checks=0
    for m in range(100):
        Q=qpoly(x,y,m); T=tpoly(x,y,m)
        assert s.expand(q-Q)==0
        assert s.expand(t-T)==0
        if m>=1: assert s.expand(Q-m*x**(m-1)-(y-x)*T)==0
        assert sum(j+1 for j in range(max(0,m-1)))==m*(m-1)//2
        q,t=s.expand(y*q+x**m),s.expand(y*t+(m*x**(m-1) if m else 0))
        checks+=4
    for n in range(1001):
        assert 0<=budget(n)==closed(n)<=F(8,9)
        if n:
            assert budget(n)==budget(n-1)+F(2*(n-1),4**(n-1))
        checks+=2
    pts=[(F(0),F(0)),(F(1,5),F(1,239)),(F(-1,5),F(1,239)),
       (F(1,2),F(-1,2)),(F(-1,2),F(1,2)),(F(1,3),F(1,6)),
       (F(-1,3),F(-1,6)),(F(1,239),F(-1,5))]
    for a,b in pts:
        assert abs(a)<=F(1,2) and abs(b)<=F(1,2)
        running=F(0)
        for n in range(33):
            if n:
                k=n-1
                if k:
                    second=numerical_t(a,b,2*k+1)
                    running+=F((-1)**k,2*k+1)*second
            assert abs(running)<=budget(n)
            checks+=1
    # Wrong second polynomial coefficient order fails for non-symmetric x,y.
    assert tpoly(x,y,3)!=y*2+x
    assert tpoly(x,y,3)==y+2*x
    print(json.dumps({'checks':checks,'symbolic_power_degrees':100,
      'exact_geometric_budgets':1001,'signed_points':len(pts),
      'signed_finite_lengths':33,'coefficient_count_proved_by_formula':True,
      'all_N_Bishop_absolute_order_proved':False,'lean_kernel_checked':False},
      sort_keys=True))

if __name__=='__main__': main()
