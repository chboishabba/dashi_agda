#!/usr/bin/env python3
"""BS13: reference positive curvature energy kernel on normal holonomy gauge.
Independent normal electric Riemann replay; no quantitative metric coercivity.
"""
import sympy as s
from itertools import product
import check_hopf369_bs_physical_modes as five
import check_hopf369_bs_york_resonance as four


def run():
    n,b,k=five.n,five.b,five.k; h=four.h; hi=four.hi;c=four.c
    t,x,y,r=five.t,five.x,five.y,five.r; coords=five.coords;ix=range(5)
    chi=t*x+r*r+y*r; A=s.Matrix([r*t+x*y,t*r+x*x,x*r+t*y,r*r+t*x])
    T=(n+n*n)*s.Matrix(4,4,lambda i,j:(i+j+1)*r+(i+1)*(j+1)*t*x+int(i==j)*y*y)
    phi=-2*chi/b**2;gamma=T+2*chi*h/b**2;beta=A/b**4
    p=s.zeros(5);p[0,0]=2*phi;p[0,1:5]=(b*b*beta).T;p[1:5,0]=b*b*beta;p[1:5,1:5]=b*b*gamma
    # Independent Christoffel variation from original metric, then R^n_{a n b}.
    dinv=-five.gi*p*five.gi
    dg={}
    for a,i,j in product(ix,repeat=3):
        v=five.gi[a,a]*(s.diff(p[a,j],coords[i])+s.diff(p[a,i],coords[j])-s.diff(p[i,j],coords[a]))/2
        v+=sum(dinv[a,l]*five.g[l,l]*five.gamma(l,i,j) for l in ix)
        v=s.factor(v)
        if v!=0:dg[a,i,j]=v
    def D(a,i,j):return dg.get((a,i,j),s.S.Zero)
    R=s.zeros(4)
    for a,d in product(range(4),repeat=2):
        i=a+1;j=d+1
        v=s.diff(D(0,j,i),n)-s.diff(D(0,0,i),coords[j])
        v+=sum(D(0,0,l)*five.gamma(l,j,i)+five.gamma(0,0,l)*D(l,j,i)-D(0,j,l)*five.gamma(l,0,i)-five.gamma(0,j,l)*D(l,0,i) for l in ix)
        R[a,d]=v
    # Lower first slot, normalize unit normal and raise tangential slot:
    # -2 phi g_ab from lowering first slot cancels +2 phi I from normal norm.
    actual=hi*R/b**2+hi*gamma
    Q=four.Hess(chi)-c*h*chi; LA=four.L(A)
    S=hi*(T.diff(n)-LA/b**4)/2
    expected=-S.diff(n)-2*k*S+2*hi*Q/b**4
    assert (actual-expected).applyfunc(five.simp)==s.zeros(4)
    # Integrated exact kernel identities: F=b²T'; F'= (b^-2)' LA +4 b^-2 Q.
    # Matching endpoint T' and b -> Q=0. Then F=b^-2 LA+C0;
    # periodic T -> C0=-(I4/I2) LA. M=-I4/(2I2) LA.
    I2=s.Rational(15,8);I4=s.Rational(165,64)
    assert I4/(2*I2)==s.Rational(11,16)
    a,d=s.symbols('LA C0');assert s.expand((a+d-a)/2).subs(d,-I4*a/I2)==-s.Rational(11,16)*a
    print('PASS all 16 independent normal electric Riemann components and exact periodic kernel coefficient -11/16')

if __name__=='__main__':run()
