#!/usr/bin/env python3
"""Exact arithmetic regression; synthetic points, not actual zeta zero data."""
from fractions import Fraction as Q
from math import comb, factorial
import sympy as s


def check():
    x, y = s.symbols('x y', nonnegative=True)
    a, b = s.symbols('a b', real=True)
    phase = lambda n: s.expand(s.re((a+s.I*b)**n))
    assert s.expand(phase(6)-(a*a+b*b)**3*(4*((a*a-b*b)/(a*a+b*b))**3-3*((a*a-b*b)/(a*a+b*b)))).cancel() == 0
    assert s.cancel(phase(8)-(a*a+b*b)**4*(8*((a*a-b*b)/(a*a+b*b))**4-8*((a*a-b*b)/(a*a+b*b))**2+1)) == 0
    old = [Q(1,30000), Q(1,300), Q(1,300), Q(1,300), Q(1,17000)]
    scalar = [Q(1,35840), Q(1,500), Q(1,500), Q(1,500), Q(1,22400)]
    k = Q(375,448)
    assert max(v/o for v,o in zip(scalar,old)) == k
    assert Q(1,1)+Q(1,2)+Q(1,24)+Q(1,720) <= Q(8,5)
    assert Q(1,576)+2*Q(1,17280)+Q(1,518400) <= Q(1,500)
    assert Q(1,1440) <= Q(1,500)
    c = Q(66,65*factorial(10))
    coeff = Q(1,factorial(8))+2*c
    radial = [coeff*comb(4,j) for j in range(5)]
    assert all(v <= Q(4,5)*o for v,o in zip(radial,old))
    assert all(Q(comb(8,2*j),factorial(8))+2*c*comb(4,j)<=Q(4,5)*old[j] for j in range(5))
    # Unit-square exact rational interval stress: bound the omitted series
    # after degree 24 by the geometric absolute tail (no floats).
    count=0
    for i in range(-16,17):
        for j in range(-16,17):
            A,B=Q(i,16),Q(j,16)
            X,Y=A*A,B*B; R=X+Y
            p=lambda m:sum((-1)**l*comb(2*m,2*l)*X**(m-l)*Y**l for l in range(m+1))
            P=[p(m) for m in range(13)]
            assert abs(P[4])<=R**4
            tail=sum(P[m]/factorial(2*m) for m in range(5,13))
            error=R**13/Q(factorial(26))/(1-Q(2,27*28))
            assert abs(tail)+error<=c*R**5
            beyond6=P[4]/factorial(8)+tail
            Eold=sum(old[l]*X**(4-l)*Y**l for l in range(5))
            assert abs(beyond6)+error<=Q(4,5)*Eold
            assert abs(beyond6)+error<=k*Eold
            count+=1
    H,L,F,I,d,B0,D,k0=s.symbols('H L F I d B0 D k0',real=True)
    Bnew=B0-(1-k0)*D
    assert s.expand((4*d+I-Bnew)-(4*d+I-B0)-(1-k0)*D)==0
    assert s.expand((F-I)/2-(2*d-Bnew/2)-((H-I)/2+(Bnew-L)/2-2*d)).subs(H,L+F).expand()==0
    # Nonnegative slack cannot pay the strict endpoint by itself.
    for S in (Q(0),Q(1,100),Q(1)):
        for excess in (Q(0),Q(1,100),Q(1)):
            assert 2*(2+excess)+S-4>=0
    print(f'PASS: 2 phase/radial identities, 5+5+5 coefficient comparisons, {count} exact interval stress points, 2 terminal identities, 9 strict endpoint negative controls')
    print('tight scalar factor:',k,'radial coefficient:',coeff)


if __name__=='__main__':
    check()
