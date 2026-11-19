#!/usr/bin/env python3
"""Backward canonical spherical exterior bound, all zero-monopole multipoles.
Uses the same exterior action as check_kk_3d_polarization_bidi.py.
No warped or physical Einstein-matter solution claimed.
"""
import sympy as s

def check():
    t=s.symbols('t',positive=True)
    f=t/(1-t)
    total=s.simplify(2*t*s.diff(t*s.diff(f,t),t)+3*t*s.diff(f,t)+f)
    expected=t*(6-3*t+t*t)/(1-t)**3
    assert s.simplify(total-expected)==0
    x=s.symbols('x',real=True)
    for n in range(1,9):
        assert s.integrate(s.legendre(n,x)**2,(x,-1,1))==s.Rational(2,2*n+1)
        for m in range(1,n):
            assert s.integrate(s.legendre(n,x)*s.legendre(m,x),(x,-1,1))==0
    a,b,w,v=s.symbols('a b w v',real=True,nonzero=True)
    assert s.expand((w*a*a+v*b*b)*(1/w+1/v)-(a+b)**2-(w*a-v*b)**2/(w*v))==0
    G=6.67430e-11;g=9.80665;R=.1375;r=.2375
    tau=(R/r)**2; S=float(expected.subs(t,tau))
    dipole=g*g*r**6/(4*G*R**3)
    optimum=dipole*6*tau/S
    print('PASS multipole sum, orthogonality, weighted CS identity')
    print('dipole J',dipole,'optimal J',optimum,'ratio',optimum/dipole)
    for L in (1,2,3,5,10,20):
        partial=sum((n+1)*(2*n+1)*tau**n for n in range(1,L+1))
        print(L,dipole*6*tau/partial)
if __name__=='__main__':check()
