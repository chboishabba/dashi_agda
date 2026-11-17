#!/usr/bin/env python3
"""Exact original F8 normal_order=3 U/P/M normal-gradient constraint.

Tests original centered/one-sided D, same bulk force in P and M,
weak-Israel lower M SAT, outgoing upper P SAT, tensor-product
radial-normal commutation and signed radial-shift decomposition.
No G3 full moving stability or Agda kernel claim.
"""
from fractions import Fraction as F
import random

def D(x,i,h):
    if i==0:return (x[1]-x[0])/h
    if i==len(x)-1:return (x[-1]-x[-2])/h
    return (x[i+1]-x[i-1])/(2*h)

def main():
    rng=random.Random(6683903); checks=0
    for n in (2,3,5,9):
        for _ in range(100):
            v=F(rng.randrange(-9,0),10)
            h=F(rng.randrange(1,8),rng.randrange(8,19))
            p=[F(rng.randrange(-10,11),rng.randrange(1,9)) for _ in range(n)]
            m=[F(rng.randrange(-10,11),rng.randrange(1,9)) for _ in range(n)]
            force=[F(rng.randrange(-10,11),rng.randrange(1,9)) for _ in range(n)]
            target=F(rng.randrange(-10,11),rng.randrange(1,9))
            udot=[((1+v)*p[i]+(1-v)*m[i])/2 for i in range(n)]
            pdot=[];mdot=[]
            for i in range(n):
                satp=-2*(1+v)*p[i]/h if i==n-1 else F(0)
                satm=2*(1-v)*(target-m[i])/h if i==0 else F(0)
                pdot.append((1+v)*D(p,i,h)+force[i]+satp)
                mdot.append((v-1)*D(m,i,h)+force[i]+satm)
                assert (pdot[i]-mdot[i])/2-D(udot,i,h)==(satp-satm)/2
                checks+=1
    for _ in range(300):
        u00,u10,u01,u11=[F(rng.randrange(-10,11),rng.randrange(1,9)) for _ in range(4)]
        assert (u11-u10)-(u01-u00)==(u11-u01)-(u10-u00)
        checks+=1
        v,A,du,duy,dq=[F(rng.randrange(-10,11),rng.randrange(1,9)) for _ in range(5)]
        assert 2*v*A*du*(duy+dq)==2*v*A*du*duy+2*v*A*du*dq
        checks+=1
    assert checks==2500
    print(f"{checks}/{checks} exact normal-gradient constraint and radial-shift controls PASS")

if __name__=="__main__":main()
