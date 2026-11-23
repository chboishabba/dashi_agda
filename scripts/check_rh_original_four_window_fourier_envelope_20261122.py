#!/usr/bin/env python3
"""Original four-window Fourier reduction; local SymPy identity regression.

Source: original Lean quarticFourWindowPairing and pole weight. Assumes
the normalized unit bump is even about its centre for the cosine-only
characteristic representation. This symmetry must be verified/ported in Lean.
Does NOT certify a finite-R sign, finite-t remainder, or actual zeta zeros.
"""
import sympy as s
F=s.Rational
lam,mu=s.symbols("lam mu",real=True)
cs=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
ws=(s.Integer(1),s.Integer(-1),lam,mu)
freqs=(1,2,3,5,6,14,15,17,18)
phi={k:s.Symbol(f"f{k}",real=True) for k in freqs}
dp={k:s.Symbol(f"d{k}",real=True) for k in (1,2)}
ddp={k:s.Symbol(f"dd{k}",real=True) for k in (1,2)}
def A(k):
    return s.expand(phi[k]*sum(w*s.cos(k*c) for w,c in zip(ws,cs)))
def M(k):
    return s.expand(sum(w*((c*c*phi[k]-ddp[k])*s.cos(k*c)
                           +2*c*dp[k]*s.sin(k*c)) for w,c in zip(ws,cs)))
A1,A2=A(1),A(2)
J=s.expand(A1*M(2)-A2*M(1))
quad=s.factor(s.diff(J,mu,2)/2)
assert s.simplify(quad-(phi[1]*ddp[2]-phi[2]*ddp[1]))==0
mu0=(13*lam-8)/(144-54*lam)
assert s.simplify(J.subs({phi[1]:1,phi[2]:1,dp[1]:0,dp[2]:0,
                           ddp[1]:0,ddp[2]:0,mu:mu0}))==0
P=s.expand(((A(15)+A(17))*A2-(A(14)+A(18))*A1)/2)
Q=s.expand(2*(A1*(A(2)+A(6))-A2*(A(3)+A(5))))
atom={v:1 for v in phi.values()}
assert s.simplify(P.subs(atom).subs(mu,mu0)-3*(2-lam)/4)==0
assert s.simplify(Q.subs(atom).subs(mu,mu0)-3*(lam-2))==0
e=s.Symbol("eps",real=True)
sub={phi[k]:1-e*k*k for k in phi}
sub.update({dp[k]:-2*e*k for k in dp})
sub.update({ddp[k]:-2*e for k in ddp})
Je=s.expand(J.subs(sub))
mu1=s.factor(-s.diff(Je,e).subs({e:0,mu:mu0})
              /s.diff(Je,mu).subs({e:0,mu:mu0}))
assert s.simplify(mu1.subs(lam,F(1,2))
                  +4*(77+2*s.sqrt(3))/(507*s.pi))==0
assert s.simplify(mu1.subs(lam,F(2,3))
                  +16*(34+3*s.sqrt(3))/(729*s.pi))==0
Pe,Qe=s.expand(P.subs(sub)),s.expand(Q.subs(sub))
def jet(expr,value):
    base=s.factor(expr.subs(e,0).subs(mu,mu0).subs(lam,value))
    lin=s.factor((s.diff(expr,e)+s.diff(expr,mu)*mu1)
                 .subs(e,0).subs(mu,mu0).subs(lam,value))
    return base,lin
pH,pHe=jet(Pe,F(1,2));pT,pTe=jet(Pe,F(2,3))
qH,qHe=jet(Qe,F(1,2));qT,qTe=jet(Qe,F(2,3))
assert s.factor(pT*qH-pH*qT)==0
assert s.factor(pT*qHe+pTe*qH-pH*qTe-pHe*qT)==F(120,13)
# Explicit bounds for any positive even normalized Y with |Y|<=R:
# |phi(k)-(1-eps*k²)| <= k^4 R^4/24
# |phi'(k)+2eps*k| <= k^3 R^4/6
# |phi''(k)+2eps| <= k² R^4/2
assert F(18**4,24)==4374
assert F(18**3,6)==972
assert F(18**2,2)==162
print("PASS quadratic J2 coefficient and original finite Fourier spectrum")
print("PASS original atomic sources; J2-moving eps coefficient +120/13")
print("PASS explicit Fourier Taylor envelopes 4374,972,162 times R^4")
print("OPEN: verify source bump symmetry, choose exact mu root, compose")
print("OPEN: finite-t uniform remainder and actual zeta signed terminal")
