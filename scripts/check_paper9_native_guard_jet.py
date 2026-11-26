#!/usr/bin/env python3
"""Exact finite arithmetic controls; not proof-kernel acceptance."""
from fractions import Fraction as Q
from sympy import symbols, expand

A, B, C = 13591409, 545140134, 640320**3
K = -C
kappa = Q(-77859659565707,19943834790540897829879824384000)
t = Q(C+1728,C)
c = 3-6*K*kappa
assert Q(36**3,6)==7776>1024
assert 3+c*t == -Q(6*A,B)*t
assert 3+(3+6*K*kappa)*t != -Q(6*A,B)*t
assert 3+(3-6*K*(kappa+1))*t != -Q(6*A,B)*t
x,y,u,w,h,j,p,l,a,b,k,z,m,m1 = symbols('x y u w h j p l a b k z m m1')
checks = [
    y*(y*u-x*w)-y*(x**3-y**2)-y*(y*u-x*w-(x**3-y**2)),
    x*(6*y*j-h*u)-h*(6*h*y*j-x*u)-6*y*j*(x-h**2),
    6*h*y*j-x*u-(6*h*(y*j-x*l)+x*(6*h*l-u)),
    B*(y*u-3*x**3-c*y**2)-y*(B*u+6*A*y)+B*Q(3,t)*(t*x**3-y**2),
    (m1+m1/15)-16*m1/15,
    6*x**2*(p*k*a*a-p*b+a)-(6*p*k*(x*a)**2-p*(6*x*x*b)+6*x*(x*a)),
]
# Fourth identity: B[3/t+c]=-6A, so residual has the stated sign.
assert all(expand(v)==0 for v in checks)
print(f'{len(checks)} symbolic identities PASS', flush=True)

def sigma(n,d):
    return sum(i**d for i in range(1,n+1) if n%i==0)

steps=0
for d in (4,6):
    for n in range(257):
        assert (n+2)**d <= 64*(n+1)**d
        steps+=1
print(f'{steps} integer coefficient growth cases PASS', flush=True)

cases=0; stages=0
for i in range(10,43):
    r=Q(1,2**i)
    for d,scale in ((4,240),(6,504)):
        part=Q(0); m0=scale*r; first=-m0
        for n in range(65):
            term=scale*sigma(n+1,d-1)*(-r)**(n+1)
            m_n=scale*(n+1)**d*r**(n+1)
            m_next=scale*(n+2)**d*r**(n+2)
            assert abs(term)<=m_n and m_next<=m_n/16
            part+=term
            assert first-m0/15 <= part-m_n/15
            assert part+m_n/15 <= first+m0/15
            if d==4:
                X=1+part
                assert Q(3,4)<=X<1
            else:
                Y=1-part
                assert 1<Y
            stages+=1
        cases+=1
    assert X**3<Y**2
    if i%8==0: print('checkpoint radius power',i,flush=True)
# At zero strict sign fails, so positivity of r is indispensable.
assert (1-Q(0))**3-(1+Q(0))**2==0
assert Q(1)-256*Q(1,1024)==Q(3,4)
assert 64*Q(1,1024)==Q(1,16)
print(f'{cases} radius/weight cases; {stages} signed telescope stages PASS; 6 exact scalar/boundary controls PASS',flush=True)
