#!/usr/bin/env python3
"""Original KSW F8 d=3,7,11 radial finite-volume exact rational checks.

Finite face Green summation, origin/first-face masses, quadratic and
quartic consistency, and a deliberately naive 3D-tensor radial FV
negative control. Original KSW owners retain attribution.
"""
import random
from fractions import Fraction as F

def W(d,j):
    return (F(2*j+1,2)**d-max(F(0),F(2*j-1,2))**d)/d
def A(d,j):
    return F(2*j+1,2)**(d-1)
def L(d,u,j):
    if j==0:
        return 2*d*(u[1]-u[0])
    return (A(d,j)*(u[j+1]-u[j]) - A(d,j-1)*(u[j]-u[j-1]))/W(d,j)

checks=0
N=9
for d in (3,7,11):
    assert all(L(d,[F(j*j) for j in range(N)],j)==2*d for j in range(N-1))
    checks+=1
    quartic=[F(j**4) for j in range(N)]
    err0=L(d,quartic,0)
    err1=L(d,quartic,1)-4*(d+2)
    assert (err0,err1)=={
        3:(F(6),F(142,13)),7:(F(14),F(37190,1093)),
        11:(F(22),F(5137278,88573))
    }[d]
    checks+=1
    assert W(d,0)*2*d==A(d,0)
    assert W(d,1)*A(d,1)/W(d,1)==A(d,1)
    assert W(d,1)*A(d,0)/W(d,1)==A(d,0)
    checks+=1
    rng=random.Random(668+d)
    for _ in range(12):
        u=[F(rng.randrange(-7,8),rng.randrange(1,9)) for _ in range(N-1)]+[F(0)]
        v=[F(rng.randrange(-7,8),rng.randrange(1,9)) for _ in range(N-1)]+[F(0)]
        lhs=sum((W(d,j)*u[j]*L(d,v,j) for j in range(N-1)),F(0))
        rhs=-sum((A(d,j)*(u[j+1]-u[j])*(v[j+1]-v[j]) for j in range(N-1)),F(0))
        assert lhs==rhs,(d,lhs,rhs)
        checks+=1

# Counterexample to the NAIVE alternate discretization.
# The original F8 solver itself evolves V with d=3+2ell instead.
H=[F(j**4) for j in range(N)]
for ell,V in ((2,[F(j*j) for j in range(N)]),(4,[F(1) for j in range(N)])):
    naive=L(3,H,1)-ell*(ell+1)*H[1]
    original=L(3+2*ell,V,1)
    assert naive-original==F(142,13)
    checks+=1
print(f"{checks}/{checks} exact original radial FV and negative-control checks passed")
