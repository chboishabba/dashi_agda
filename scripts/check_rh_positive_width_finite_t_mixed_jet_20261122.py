#!/usr/bin/env python3
"""RH P0: two-parameter finite-t/smooth even-bump jets for ORIGINAL four-window source.

u=pi/t; eps=E[Y²]/2. Expand at a=0,q=4, with J2=0
maintained by mu(eps) for each lambda=1/2,2/3.
Exact source cosh(8*x/t)*cos(16*x)*cos(c*x).
Only symbolic local jet coefficients, not compact-bump remainder,
finite-t positivity, zeta zero occupancy, or signed terminal.
"""
import sympy as s
x,e,u,L,m=s.symbols("x e u L m",real=True)
F=s.Rational
cs=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
ws=(s.Integer(1),s.Integer(-1),L,m)
def pairing(w):
    d=s.diff(w,x,2)
    return (sum(wt*w.subs(x,c) for wt,c in zip(ws,cs)),
            sum(wt*d.subs(x,c) for wt,c in zip(ws,cs)))
a1,a1e=pairing(s.cos(x))
a2,a2e=pairing(s.cos(2*x))
j1,j1e=pairing(x*x*s.cos(x))
j2,j2e=pairing(x*x*s.cos(2*x))
J0=s.expand(a1*j2-a2*j1)
Je=s.expand(a1e*j2+a1*j2e-a2e*j1-a2*j1e)
mu0=(13*L-8)/(144-54*L)
assert s.factor(J0.subs(m,mu0))==0
mu1=s.factor(-Je.subs(m,mu0)/s.diff(J0,m).subs(m,mu0))
assert s.simplify((Je+s.diff(J0,m)*mu1).subs(m,mu0))==0
k1,k1e=pairing(s.cos(2*x)*s.cos(4*x))
k2,k2e=pairing(s.cos(x)*s.cos(4*x))
K0=s.expand(4*(a1*k1-a2*k2))
Ke=s.expand(4*(a1e*k1+a1*k1e-a2e*k2-a2*k2e))
def pole(cosh_poly):
    b1,b1e=pairing(cosh_poly*s.cos(16*x)*s.cos(x))
    b2,b2e=pairing(cosh_poly*s.cos(16*x)*s.cos(2*x))
    return (s.expand(b1*a2-b2*a1),
            s.expand(b1e*a2+b1*a2e-b2e*a1-b2*a1e))
p0,p0e=pole(s.Integer(1))
p2,p2e=pole(32*x*x/s.pi**2)
def jet(v,ve,l):
    mu=mu0.subs(L,l)
    return (s.factor(v.subs({L:l,m:mu})),
            s.factor((ve+s.diff(v,m)*mu1).subs({L:l,m:mu})))
h,t=F(1,2),F(2,3)
kh,khe=jet(K0,Ke,h)
kt,kte=jet(K0,Ke,t)
ph,phe=jet(p0,p0e,h)
pt,pte=jet(p0,p0e,t)
ph2,ph2e=jet(p2,p2e,h)
pt2,pt2e=jet(p2,p2e,t)
def cross(a,b,c,d):
    return s.factor(a*c-b*d)
atomic0=cross(pt,ph,kh,kt)
atomic2=cross(pt2,ph2,kh,kt)
eps0=s.factor(pt*khe+pte*kh-ph*kte-phe*kt)
eps2=s.factor(pt2*khe+pt2e*kh-ph2*kte-ph2e*kt)
assert ph==F(9,8) and pt==1
assert kh==-F(9,2) and kt==-4
assert atomic0==atomic2==0
assert eps0==F(120,13)
assert s.simplify(eps2-640*(2*s.pi-s.sqrt(3))/(39*s.pi))==0
assert eps2.is_positive
print("PASS: original J2 mu transport, finite-pole cosh expansion")
print("PASS: atomic u^0=0, atomic u^2=0")
print("PASS: eps coefficient 120/13")
print("PASS: eps*u² coefficient 640*(2*pi-sqrt(3))/(39*pi) > 0")
print("OPEN: actual selected bump remainder bounds, all-t sign, original zero sum with slack")
