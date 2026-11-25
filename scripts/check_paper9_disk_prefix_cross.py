#!/usr/bin/env python3
"""Exact local reference for Paper 9 disk-germ and literal rational cross.
Finite execution is not a native proof or full CM163 Laurent replay.
"""
from fractions import Fraction as F
from math import isqrt
import sympy as s

A0,B0,C0=13591409,545140134,640320**3

def main():
    w,a,b,d,r,t,P2,P3,S2,S3=s.symbols('w a b d r t P2 P3 S2 S3')
    L=d/(1-w); A=a*d; B=a*d+b*d*d/2
    X=a*L+b*w*L**2/2+w*w*L**3*r
    assert s.simplify(X.subs(w,0)-A)==0
    assert s.simplify(s.diff(X,w).subs(w,0)-B)==0
    assert s.cancel(w*X-(a*w*L+b*(w*L)**2/2+(w*L)**3*r))==0
    z=s.symbols('z'); m=z*z-t*z+1; inv=t-z
    xp=z*(A+B*z*w); xm=inv*(A+B*inv*w); xx=A+B*w
    red=lambda f:s.rem(s.expand(f),m,z)
    N=red(xp*xm); M=red((xx-xp)*(xx-xm)); c=2-t
    for poly,v0,v1 in [(N,A*A,t*A*B),(M,c*A*A,c*(2+t)*A*B)]:
        assert s.expand(poly.coeff(w,0)-v0)==0
        assert s.expand(poly.coeff(w,1)-v1)==0
    cross=s.expand((N*(P2+P3*A*w)-M*(S2+S3*A*w))*xx**2-N*M*xx*w*S3)
    assert s.expand(cross.coeff(w,0)-A**4*(P2-c*S2))==0
    assert s.expand(cross.coeff(w,1).subs(P2,c*S2)-A**3*(A*A*(P3-2*c*S3)-2*c*B*S2))==0
    n=s.symbols('n', nonnegative=True, integer=True)
    mag=24*(2*n+1)*(6*n+1)*(6*n+5)
    wt=A0+B0*n
    gap=C0*(n+1)**3*wt-2**41*mag*(wt+B0)
    assert all(v>0 for v in s.Poly(gap,n).all_coeffs())
    print('9 symbolic germ/cross identities and all-index signed gap polynomial PASS')
    # Literal raw integer recurrence; no floating point or decimal pi.
    sums=[F(0)]; pp,qq,tt=1,1,0
    for j in range(20):
        p,q=(1,1) if j==0 else (-24*(2*j-1)*(6*j-5)*(6*j-1),C0*j**3)
        pp*=p; qq*=q; tt=tt*q+pp*(A0+B0*j)
        sums.append(F(tt,qq))
    for j in range(1,len(sums)-1):
        lo,hi=sorted(sums[j-1:j+1]); assert lo<=sums[j+1]<=hi
    assert all(v>0 for v in sums[1:])
    m=F(0)
    for k in range(513):
        cutoff=1+(k+4)//41
        lo,hi=sorted(sums[cutoff:cutoff+2])
        scale=2**(k+2); root=isqrt(10005*scale*scale)
        assert root*root<=10005*scale*scale<(root+1)**2
        l=F(426880*root,scale)/hi; u=F(426880*(root+1),scale)/lo
        e=F(22,7) if k==0 else F(4,25**k)
        assert l<=m+e and m<=u+e
        assert u-l<=F(1,2**k)
        m+=F((-1)**k,2*k+1)*(F(16,5**(2*k+1))-F(4,239**(2*k+1)))
    print('19 adjacent prefix nesting controls, 20 positive prefixes, 513 literal cross and width checks PASS')

if __name__=='__main__':
    main()
