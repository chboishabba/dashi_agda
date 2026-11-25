#!/usr/bin/env python3
"""Exact Paper9 nested source windows and two consumer-specific transfers."""
from fractions import Fraction as F
from math import isqrt
import sympy as s

A,B,C=13591409,545140134,640320**3

def main():
    # The literal factorial prefix, not a decimal pi oracle.
    P,Q,T=1,1,0
    sums=[F(0)]
    for j in range(30):
        p,q=(1,1) if j==0 else (-24*(2*j-1)*(6*j-5)*(6*j-1),C*j**3)
        P*=p;Q*=q;T=T*q+P*(A+B*j);sums.append(F(T,Q))
    for n in range(29):
        rho=F(24*(2*n+1)*(6*n+1)*(6*n+5)*(A+B*(n+1)),C*(n+1)**3*(A+B*n))
        assert 0<rho<F(1,2**41)
        assert sums[n+2]==rho*sums[n]+(1-rho)*sums[n+1]
    windows=[];machin=[];m=F(0);last=None
    for k in range(513):
        n=1+(k+4)//41;scale=2**(k+2);r=isqrt(10005*scale**2)
        assert r*r<=10005*scale**2<(r+1)**2
        if last is not None:assert r in (2*last,2*last+1)
        last=r
        lo,hi=sorted(sums[n:n+2]);l,u=F(426880*r,scale)/hi,F(426880*(r+1),scale)/lo
        e=F(22,7) if k==0 else F(4,25**k)
        a,b=m-e,m+e;windows.append((l,u));machin.append((a,b))
        assert l<=b and a<=u
        if k:
            L,U=windows[k-1];assert L<=l<=u<=U
            if k>1:
                aa,bb=machin[k-1];assert aa<=a<=b<=bb
        m+=F((-1)**k,2*k+1)*(F(16,5**(2*k+1))-F(4,239**(2*k+1)))
    assert windows[0][0]==F(42688000,13591409)
    assert F(22,7)-windows[0][0]==F(194998,95139863)
    assert machin[1][1]>machin[0][1] # zero-stage exception
    print('29 convex edges, 512 root/window refinements, 511 Machin refinements, 513 overlap controls PASS')
    x,y=s.symbols('x y');u=x+y;v=x*y
    # Real even phase Re(a+i delta)^(2m) in squared coordinates x=a^2,y=delta^2.
    from math import comb
    for m in range(1,13):
        f=sum((-1)**j*comb(2*m,2*j)*x**(m-j)*y**j for j in range(m+1))
        assert s.expand(f.subs({x:y,y:x},simultaneous=True)-(-1)**m*f)==0
        parity=m%2;d=m-parity
        basis=[(x-y)**parity*u**(d-2*j)*v**j for j in range(d//2+1)]
        obs=s.Matrix([[g.subs({x:1,y:0}) for g in basis],[g.subs({x:1,y:1}) for g in basis]])
        ker=x*y*(x-y)**(1 if parity else 2)
        for z in obs.nullspace():
            g=s.expand(sum(c*b for c,b in zip(z,basis)))
            assert s.Poly(g,x,y).rem(s.Poly(ker,x,y)).is_zero
        assert len(obs.nullspace())==(max(0,(m-1)//2) if parity else max(0,m//2-1))
    assert (x*y*(x-y)).subs({x:1,y:2})==-2
    assert (x*y*(x-y)**2).subs({x:1,y:2})==2
    print('12 phase symmetry and exact kernel rank/divisibility layers; sixth/eighth transverse controls PASS')
    # Strict relative signed contrast: all nonnegative integer child counts.
    count=0
    for n in range(1,9):
        cap=2**n;eta=F(1,2*cap)
        for c0 in range(cap+1):
            for c1 in range(cap-c0+1):
                if c0+c1==0:continue
                d=F(c0-c1,c0+c1)
                for c,h in [(c0,eta),(c1,-eta)]:
                    if c:assert abs(h-d)<1
                    else:assert abs(h-d)>1
                # Exact boundary: estimate zero at a unique live child has error 1.
                if not c0 or not c1:assert abs(d)==1
                count+=1
    print(count,'integer child-count pairs; strict selector reverse, zero and equality controls PASS')
if __name__=='__main__':main()
