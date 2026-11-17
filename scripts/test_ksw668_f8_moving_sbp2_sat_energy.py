#!/usr/bin/env python3
"""Exact original normal_order=3 F8 SBP2/SAT characteristic energy.

Tests the ACTUAL one-sided endpoint + centered interior difference,
H=dy*diag(1/2,1,...,1,1/2), lower M-SAT, upper P-SAT,
t=4/3 moving Israel source cap, and remaining radial-shift/warp terms.
NOT a full z^-3-weighted, time-dependent radial/normal SSPRK3 energy proof.
"""
from fractions import Fraction as F
import random

def D(x, i, dy):
    if i == 0: return (x[1]-x[0])/dy
    if i == len(x)-1: return (x[-1]-x[-2])/dy
    return (x[i+1]-x[i-1])/(2*dy)

def test():
    rng=random.Random(66838)
    count=0
    for n in (2,3,4,6,12):
        for _ in range(120):
            dy=F(rng.randrange(1,7),rng.randrange(3,19))
            P=[F(rng.randrange(-9,10),rng.randrange(1,11)) for _ in range(n)]
            M=[F(rng.randrange(-9,10),rng.randrange(1,11)) for _ in range(n)]
            v=F(rng.randrange(-9,10),10)
            target=F(rng.randrange(-9,10),rng.randrange(1,11))
            a=1+v;b=1-v
            weights=[F(1,2) if i in (0,n-1) else F(1) for i in range(n)]
            rhsP=[a*D(P,i,dy)-(2*a/dy*P[i] if i==n-1 else 0) for i in range(n)]
            rhsM=[(v-1)*D(M,i,dy)+(2*b/dy*(target-M[i]) if i==0 else 0) for i in range(n)]
            power=dy*sum((weights[i]*(P[i]*rhsP[i]+M[i]*rhsM[i]) for i in range(n)),F(0))
            closed=-a/2*(P[0]**2+P[-1]**2)-b/2*(M[-1]**2+(M[0]-target)**2)+b/2*target**2
            assert power==closed,(n,power,closed)
            count+=1
    for _ in range(300):
        p,m,pn,mn,s=[F(rng.randrange(-12,13),rng.randrange(1,10)) for _ in range(5)]
        v=-F(3,5);target=p/4-F(5,4)*s
        boundary=-F(1,5)*(p*p+pn*pn)-F(4,5)*(mn*mn+(m-target)**2)+F(4,5)*target**2
        completed=(-F(4,5)*(m-target)**2-F(3,20)*(p+F(5,3)*s)**2
                    +F(5,3)*s*s-F(1,5)*pn*pn-F(4,5)*mn*mn)
        assert boundary==completed
        count+=1
    for _ in range(300):
        a,ul,ur,pl,pr,ml,mr,v,invz=[F(rng.randrange(-9,10),rng.randrange(1,9)) for _ in range(9)]
        du=ur-ul;dp=pr-pl;dm=mr-ml
        assert a*du*((1+v)*dp+(1-v)*dm)-a*du*(dp+dm)==a*v*du*(dp-dm)
        p,m=[F(rng.randrange(-9,10),rng.randrange(1,9)) for _ in range(2)]
        assert F(1,2)*(p+m)*(-F(3,2)*invz*(p-m))==-F(3,4)*invz*(p*p-m*m)
        count+=2
    assert count==1500
    print(f"{count}/{count} exact original SBP2/SAT, source cap, radial shift and warp checks PASS")

if __name__=="__main__": test()
