#!/usr/bin/env python3
"""RH P0/A2 original four-window atomic biharmonic geometry, exact SymPy.

Only original Lean atomic J2/pole/source definitions are consumed.
Negative-square Fourier factor is specific to ATOMIC HIGH-POLE vertex.
No claim for positive-radius, finite-t, actual zeros, or all six cube faces.
"""
import sympy as s
Q=s.Rational
lam,mu,q,S,L,eta,v,ell=s.symbols("lam mu q S L eta v ell",real=True)
cs=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
w=(s.Integer(1),s.Integer(-1),lam,mu)
A=lambda k:s.trigsimp(sum(x*s.cos(k*c) for x,c in zip(w,cs)))
M=lambda k:s.trigsimp(sum(x*c*c*s.cos(k*c) for x,c in zip(w,cs)))
a1,a2=A(1),A(2)
assert s.simplify(a1-(Q(1,2)-mu))==0
assert s.simplify(a2-(Q(3,2)-lam+mu))==0
assert s.simplify(M(1)/s.pi**2+Q(1,18)+mu)==0
assert s.simplify(M(2)/s.pi**2-Q(1,18)+lam/4-mu)==0
J=s.factor((a1*M(2)-a2*M(1))/s.pi**2)
assert s.simplify(J+(54*lam*mu+13*lam-144*mu-8)/72)==0
assert Q(1,8)+Q(1,18)==Q(13,72)
mu0=(13*lam-8)/(144-54*lam)
assert s.simplify(J.subs(mu,mu0))==0
assert s.simplify(mu0.subs(lam,Q(1,2)))==-Q(1,78)
assert s.simplify(mu0.subs(lam,Q(2,3)))==Q(1,162)
def source(l):
    m=mu0.subs(lam,l)
    weights=[x.subs({lam:l,mu:m}) for x in w]
    x1,x2=a1.subs({lam:l,mu:m}),a2.subs({lam:l,mu:m})
    masses=[s.simplify(4*x*(x1*s.cos(2*c)-x2*s.cos(c))) for x,c in zip(weights,cs)]
    b1=s.trigsimp(sum(x*s.cos(16*c)*s.cos(c) for x,c in zip(weights,cs)))
    b2=s.trigsimp(sum(x*s.cos(16*c)*s.cos(2*c) for x,c in zip(weights,cs)))
    return s.factor(b1*x2-b2*x1), masses
ph,mh=source(Q(1,2)); pt,mt=source(Q(2,3))
assert (ph,pt)==(Q(9,8),s.Integer(1))
mass=[s.factor(pt*x-ph*y) for x,y in zip(mh,mt)]
assert mass==[-Q(40,117),0,Q(160,351),-Q(40,351)]
assert mass==[Q(40,351)*x for x in (-3,0,4,-1)]
assert mh[1]==3 and mt[1]==Q(8,3) and mass[1]==0
assert s.simplify(sum(mass))==0
assert s.simplify(sum(x*c**2 for x,c in zip(mass,cs)))==0
F=sum(x*s.cos(q*c) for x,c in zip(mass,cs))
assert s.trigsimp(F+Q(80,351)*(1-s.cos(s.pi*q/2))**2)==0
assert s.trigsimp(F+Q(320,351)*s.sin(s.pi*q/4)**4,method="fu")==0
xs=(-s.pi,-s.pi/2,s.Integer(0),s.pi/2,s.pi)
five=[Q(20,351)*k for k in (-1,4,-6,4,-1)]
assert s.trigsimp(sum(x*s.cos(q*c) for x,c in zip(five,xs))-F)==0
for k in range(4):
    assert s.simplify(sum(x*c**k for x,c in zip(five,xs)))==0
for k in range(4):
    assert s.simplify(s.diff(F,q,k).subs(q,4))==0
assert s.simplify(s.diff(F,q,4).subs(q,4)/24+5*s.pi**4/1404)==0
assert s.simplify(F.subs(q,1))==-Q(80,351)
sourceS=s.simplify(-sum(x*c**4 for x,c in zip(mass,cs))/4)
sourceM6=s.simplify(sum(x*c**6 for x,c in zip(mass,cs)))
sourceL=s.simplify(sum(abs(x)*s.cosh(c)*c**5 for x,c in zip(mass,cs)))
assert sourceS==5*s.pi**4/234
assert sourceM6==-25*s.pi**6/234
assert s.simplify(sourceL-
    5*s.pi**5*(s.cosh(s.pi/2)+8*s.cosh(s.pi))/351)==0
r=eta*v
NZ=2*r*ell
gain=S/(6*v**6)*Q(2,5)*r**5*ell
sixth=Q(3,20)*s.pi**6*r**6*NZ/(720*v**8)
eighth=eta**(-2)*L*r**8*NZ/(17000*v**10)
lead=s.factor((sixth+eighth-gain)/(eta**5*ell/v))
assert s.factor(lead-(-S/15+s.pi**6*eta**2/2400+L*eta**2/8500))==0
assert s.factor(15*(lead+S/15)
     -(s.pi**6*eta**2/160+3*L*eta**2/1700))==0
assert Q(2,35840)==Q(1,17920)<Q(1,17000)
print("PASS exact original atomic J2, 13/72 geometric cofactor and endpoint roots")
print("PASS P_half=9/8, P_two=1, observed pi/3 cancellation")
print("PASS (-3,0,4,-1) folded negative 5-point biharmonic stencil")
print("PASS F(q)=-320/351*sin(pi*q/4)^4; q=4 fourth-order spectral notch")
print("PASS original S, M6 and fifth absolute hyperbolic moment L")
print("PASS A2 leading coefficient denominators 15, 2400, 8500, 160, 1700")
print("OPEN positive-radius witness, finite pole, signed FarExact and RH/GRH")
