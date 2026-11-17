#!/usr/bin/env python3
"""Exact original F8 radial FV / physical reconstruction with origin trace.

Original coefficients d=3,7,11, including weak-SAT stage linearity.
This is NOT a full 3D TT tensor norm, Agda kernel or SSPRK3 stability.
"""
from fractions import Fraction as F
import random
rng=random.Random(66837)
def W(d,j):
    a=F(2*j+1,2);b=F(max(0,2*j-1),2)
    return (a**d-b**d)/d
def cp(d,j):return F(2*j+1,2)**(d-1)/W(d,j)
def cm(d,j):return F(2*j-1,2)**(d-1)/W(d,j)
def fv(d,v,j):
    if j==0:return 2*d*(v[1]-v[0])
    return cp(d,j)*(v[j+1]-v[j])-cm(d,j)*(v[j]-v[j-1])
def lift(v,j,ell,lam=F(1)):
    return lam*j**ell*v[j]
def induced(d,ell,vs,j,lam):
    hs=[lift(vs,k,ell,lam) for k in range(len(vs))]
    if not ell:return fv(d,hs,j)
    if j==0:return F(0)
    if j==1:
        return cp(d,1)*(hs[2]/2**ell-hs[1])-cm(d,1)*(hs[1]-lam*vs[0])
    return cp(d,j)*(F(j,j+1)**ell*hs[j+1]-hs[j])-cm(d,j)*(hs[j]-F(j,j-1)**ell*hs[j-1])
def stage(v,p,m,radial,dp,dm,invz,invdy,target,lower_sat,upper_sat):
    force=radial-F(3,2)*invz*(p-m)
    u=F(1,2)*((1+v)*p+(1-v)*m)
    pp=(1+v)*dp+force
    mm=(v-1)*dm+force
    if upper_sat:pp-=2*(1+v)*invdy*p
    if lower_sat:mm+=2*(1-v)*invdy*(target-m)
    return (u,pp,mm)
checks=0
for ell,d in [(0,3),(2,7),(4,11)]:
    for _ in range(30):
        v=[F(rng.randrange(-11,12),rng.randrange(1,9)) for _ in range(10)]
        lam=F(rng.randrange(1,10),rng.randrange(1,9))
        for j in range(9):
            assert induced(d,ell,v,j,lam)==lam*j**ell*fv(d,v,j),(ell,j)
            checks+=1
    if ell:
        v=[F(1)]+[F(0)]*9
        assert all(lift(v,j,ell)==0 for j in range(10))
        assert induced(d,ell,v,1,F(1))==cm(d,1)
        assert cm(d,1)=={2:F(7,1093),4:F(11,88573)}[ell]
        checks+=1
        for _ in range(60):
            v=[F(rng.randrange(-12,13),rng.randrange(1,10)) for _ in range(10)]
            j=rng.randrange(2,9)
            lam=F(rng.randrange(1,7),rng.randrange(1,8))
            next_ratio=F(rng.randrange(1,8),rng.randrange(1,8))
            prev_ratio=F(rng.randrange(1,8),rng.randrange(1,8))
            hp=lam*F(j-1,j)**ell*v[j-1];hj=lam*v[j];hn=lam*F(j+1,j)**ell*v[j+1]
            lhs=cp(d,j)*(next_ratio*hn-hj)-cm(d,j)*(hj-prev_ratio*hp)-lam*fv(d,v,j)
            rhs=cp(d,j)*(next_ratio*lam*F(j+1,j)**ell-lam)*v[j+1]+cm(d,j)*(prev_ratio*lam*F(j-1,j)**ell-lam)*v[j-1]
            assert lhs==rhs;checks+=1
for _ in range(100):
    v,p,m,radial,dp,dm,invz,invdy,target=[F(rng.randrange(-9,10),rng.randrange(1,8)) for _ in range(9)]
    lam=F(rng.randrange(1,9),rng.randrange(1,8))
    for lower,upper in [(False,False),(True,False),(False,True)]:
        got=stage(v,lam*p,lam*m,lam*radial,lam*dp,lam*dm,invz,invdy,lam*target,lower,upper)
        expected=tuple(lam*a for a in stage(v,p,m,radial,dp,dm,invz,invdy,target,lower,upper))
        assert got==expected;checks+=1
print(f"{checks}/{checks} exact F8 FV-origin and original U/P/M weak-SAT scaling tests PASS")
print("origin H indistinguishable: ell2 delta force 7/1093; ell4 11/88573 at unit h, eps")
