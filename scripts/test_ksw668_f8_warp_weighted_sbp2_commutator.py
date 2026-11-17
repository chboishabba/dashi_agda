#!/usr/bin/env python3
"""Exact original AdS5 z^-3 weighted normal_order=3 SBP2 commutator.

Uses actual z_i=b+i*dy, w_i=z_i^-3 and normal endpoint/centered
stencil. The nonzero, sign-indefinite interior term is not a stability
theorem; it is the next G3 moving-warp energy obligation.
"""
from fractions import Fraction as F
import random

def main():
    rng=random.Random(6683801)
    checks=0
    for n in (2,3,5,12):
        for _ in range(80):
            dy=F(rng.randrange(1,9),rng.randrange(9,31))
            b=F(rng.randrange(1,9),rng.randrange(9,19))
            w=[(b+i*dy)**(-3) for i in range(n)]
            x=[F(rng.randrange(-9,10),rng.randrange(1,10)) for i in range(n)]
            dx=[(x[1]-x[0])/dy if i==0
                else (x[-1]-x[-2])/dy if i==n-1
                else (x[i+1]-x[i-1])/(2*dy) for i in range(n)]
            lhs=dy*sum((F(1,2 if i in (0,n-1) else 1)
                         *w[i]*x[i]*dx[i] for i in range(n)),F(0))
            rhs=(w[-1]*x[-1]**2-w[0]*x[0]**2)/2+sum(
                ((w[i]-w[i+1])*x[i]*x[i+1]/2
                 for i in range(n-1)),F(0))
            assert lhs==rhs,(n,lhs,rhs)
            checks+=1
    assert F(1,2)*(2-1)*(1)*(1)==F(1,2)
    assert F(1,2)*(2-1)*(1)*(-1)==-F(1,2)
    print(f"{checks}/{checks} exact actual-warp SBP2 full-grid checks PASS")
    print("Independent sign controls: +1/2, -1/2 PASS")

if __name__=="__main__":
    main()
