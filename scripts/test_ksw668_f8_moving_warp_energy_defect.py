#!/usr/bin/env python3
"""Exact original F8 moving z^-3 SBP2/SAT energy and face-bound audit.

Same original normal_order=3 centered/one-sided D, z_i=b+i*dy,
w_i=z_i^-3, b_T=v, force=-3(P-M)/(2z).
Tests FINITE energy ledger; no radial energy or SSPRK3 stability claim.
"""
from fractions import Fraction as F
import random

def D(x, i, h):
    if i==0:return (x[1]-x[0])/h
    if i==len(x)-1:return (x[-1]-x[-2])/h
    return (x[i+1]-x[i-1])/(2*h)

def main():
    rng=random.Random(66839);count=0
    for n in (2,3,4,7,13):
        for _ in range(80):
            b=F(rng.randint(1,13),rng.randint(5,19))
            h=b*F(rng.randint(1,10),rng.randint(10,20))
            v=F(rng.randint(-9,-1),10)
            p=[F(rng.randint(-12,12),rng.randint(1,11)) for _ in range(n)]
            m=[F(rng.randint(-12,12),rng.randint(1,11)) for _ in range(n)]
            target=F(rng.randint(-9,9),rng.randint(1,12))
            z=[b+i*h for i in range(n)];w=[q**(-3) for q in z]
            nu=[F(1,2) if i in (0,n-1) else F(1) for i in range(n)]
            a=1+v; speedM=v-1
            dp=[a*D(p,i,h)-F(3,2)*(p[i]-m[i])/z[i]
                -(2*a*p[i]/h if i==n-1 else 0) for i in range(n)]
            dm=[speedM*D(m,i,h)-F(3,2)*(p[i]-m[i])/z[i]
                +(2*(1-v)*(target-m[i])/h if i==0 else 0)
                for i in range(n)]
            kinetic=h*sum((nu[i]*w[i]*(p[i]*dp[i]+m[i]*dm[i])
                           for i in range(n)),F(0))
            weightTime=-F(3,2)*v*h*sum(
                (nu[i]*w[i]/z[i]*(p[i]**2+m[i]**2) for i in range(n)),F(0))
            boundary=(w[0]*(-a*p[0]**2/2-(1-v)*(m[0]-target)**2/2+
                            (1-v)*target**2/2)
                      +w[-1]*(-a*p[-1]**2/2-(1-v)*m[-1]**2/2))
            cp=sum(((w[i]-w[i+1])*p[i]*p[i+1]/2 for i in range(n-1)),F(0))
            cm=sum(((w[i]-w[i+1])*m[i]*m[i+1]/2 for i in range(n-1)),F(0))
            jp=h*sum((nu[i]*w[i]/z[i]*p[i]**2 for i in range(n)),F(0))
            jm=h*sum((nu[i]*w[i]/z[i]*m[i]**2 for i in range(n)),F(0))
            defect=a*(cp-F(3,2)*jp)-(1-v)*(cm-F(3,2)*jm)
            assert kinetic+weightTime==boundary+defect
            count+=1
            for x,c in ((p,cp),(m,cm)):
                E=h/2*sum((nu[i]*w[i]*x[i]**2 for i in range(n)),F(0))
                assert abs(c)<=3*E/b
                count+=1
            for i in range(n-1):
                dw=w[i]-w[i+1]
                assert dw*dw*b*b<=9*h*h*w[i]*w[i+1]
                count+=1
    for t in (F(0),F(1,100),F(1,2),F(1)):
        gap=9*(1+t)**3-(3+3*t+t*t)**2
        assert gap==t*(9+12*t+2*t*t+t*t*(1-t)) and gap>=0
        count+=1
    assert count==3124
    print(f"{count}/{count} moving-warp exact-rational energy and face-bound tests PASS")

if __name__=="__main__":main()
