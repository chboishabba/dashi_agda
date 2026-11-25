#!/usr/bin/env python3
from fractions import Fraction as Q
from math import factorial
import sympy as s


def check():
    a,d,u,r=s.symbols('a d u r', real=True)
    p=lambda n:s.expand(s.re((a+s.I*d)**n))
    p6,p8=p(6),p(8)
    assert s.expand(p6-(a**6-d**6-15*a*a*d*d*(a*a-d*d)))==0
    assert s.expand(p8-((a**4-d**4)**2+16*a**4*d**4-28*a*a*d*d*(a*a-d*d)**2))==0
    for n in (6,8):
        assert s.expand(p(n).subs({a:a/r,d:d/r})*r**n-p(n))==0
        assert s.expand(p(n).subs(a,-a)-p(n))==0
    f=s.series(s.cosh(a*u)*s.cos(d*u),u,0,10).removeO().expand()
    for n in range(0,10,2):
        assert s.expand(f.coeff(u,n)-p(n)/factorial(n))==0
    # Local |(alpha+i q)u|^2 <= 2. Tail term ratio <= 1/66.
    assert Q(2,11*12)==Q(1,66)
    factor=Q(66,65*factorial(10))
    for k in range(5,100):
        assert Q(2,(2*k+1)*(2*k+2))<=Q(1,66)
    for x in (Q(0),Q(1,16),Q(1,4),Q(1),Q(2)):
        assert sum(x**k/Q(factorial(2*k)) for k in range(5,100))<=factor*x**5
    # Literal guarded sums: source tags retained, no swapping a and delta.
    rows=[('chi1',Q(1,2),Q(1,4),2),('chi1',Q(-1,2),Q(1,4),2),
          ('chi1',Q(0),Q(1,4),3),('chi1',Q(1,2),Q(0),7),
          ('chi1',Q(1,2),Q(9),1),('chi2',Q(1,2),Q(1,4),4)]
    local=[(a,d,m) for chi,a,d,m in rows if chi=='chi1' and 0<abs(d)<=1]
    A=sum(m*(a**6-d**6) for a,d,m in local)
    C=sum(m*a*a*d*d*(a*a-d*d) for a,d,m in local)
    B=sum(m*(a**4-d**4)**2 for a,d,m in local)
    D=sum(m*a**4*d**4 for a,d,m in local)
    E=sum(m*a*a*d*d*(a*a-d*d)**2 for a,d,m in local)
    def phase(n,a,d):
        return sum((-1)**j*s.binomial(n,2*j)*a**(n-2*j)*d**(2*j) for j in range(n//2+1))
    assert sum(m*phase(6,a,d) for a,d,m in local)==A-15*C
    assert sum(m*phase(8,a,d) for a,d,m in local)==B+16*D-28*E
    assert C>0 and E>0  # actual horizontal reflection reinforces both
    print('PASS: 2 physical phase charts, 4 scale/reflection identities, 5 Taylor coefficients, 95 tail ratios, 5 exact tail controls, 2 guarded moment sums and reflection non-cancellation')


if __name__=='__main__':
    check()
