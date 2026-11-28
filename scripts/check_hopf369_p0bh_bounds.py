"""Exact rational interval envelope for the original BG trial; not the BH lift."""
from fractions import Fraction as F
from pathlib import Path
import json,sys
import numpy as np
import sympy as s

def bound(co,lo,hi):
    l=h=F(float(co[-1]))
    for t in co[-2::-1]:
        z=[l*lo,l*hi,h*lo,h*hi]; l=min(z)+F(float(t));h=max(z)+F(float(t))
    return max(abs(l),abs(h))

def run(c):
    a=c[:180].reshape(9,4,5);b=c[180:].reshape(9,4,2);mx=F(0)
    # r below denotes squared coordinate radius; s=r/(.1+r).
    # AY lift <=1, absolute trig modes <=1, L^2<2.
    # max of BG endpoint polynomial is L^2*(2/5)^2*(3/5)^3/2.
    for k in range(512):
        l=F(k,512);h=F(k+1,512);lo=l/(F(1,10)+l);hi=h/(F(1,10)+h)
        H=[1,1,1,1,h/2,h/2,h/2,h,2*h];fac=(1-l)**2/(1+10*l)
        z=fac*sum(H[i]*(sum(bound(a[i,:,j],lo,hi) for j in range(5))+F(108,3125)*sum(bound(b[i,:,j],lo,hi) for j in range(2))) for i in range(9));mx=max(mx,z)
    assert mx<F(51,1000)
    print('BG global rational envelope < 51/1000; computed bound',float(mx))
    z=s.symbols('z');P=z*z*(1-z)**5/2
    assert s.integrate(P**2,(z,0,1))==s.Rational(1,60060)
    assert s.integrate(s.diff(P,z,2)**2,(z,0,1))==s.Rational(10,231)
    assert s.integrate(s.diff(P,z,3)**2,(z,0,1))==s.Rational(85,7)
    assert s.integrate(s.diff(P,z,2),(z,0,1))==0
    assert s.diff(P,z,2).subs(z,0)==1
    assert all(s.diff(P,z,k).subs(z,1)==0 for k in range(5))
    print('PASS exact collar energy scaling and endpoint jets')
if __name__=='__main__':
    c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));assert len(c)==252
    run(c)
