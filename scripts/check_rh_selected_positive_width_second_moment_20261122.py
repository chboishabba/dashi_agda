#!/usr/bin/env python3
"""RH P0: positive-width even-bump SECOND-MOMENT jet at q=4.

Derived from the ORIGINAL four-window source pairings (Lean main):
  Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean
  Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean
  Synthesis/RiemannProjectiveQuarticFourWindowAtomic.lean
This is formal small-radius Taylor algebra around symmetric normalized bumps,
not acceptance of the actual Lean bump, finite-t sign, or zeta-zero payment.

eps = E[Y**2]/2; E[f(c+Y)] = f(c)+eps*f''(c)+O(E[Y**4]).
Allow mu(lambda,eps) to move to preserve original J2=0 exactly to O(eps).
"""
import sympy as s

x,eps=s.symbols("x eps",real=True)
L,m=s.symbols("L m",real=True)
F=s.Rational
centres=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
weights=(s.Integer(1),s.Integer(-1),L,m)

def pairing(w):
    second=s.diff(w,x,2)
    return s.expand(sum(a*(w.subs(x,c)+eps*second.subs(x,c))
                        for a,c in zip(weights,centres)))

A1=pairing(s.cos(x)); A2=pairing(s.cos(2*x))
M1=pairing(x*x*s.cos(x)); M2=pairing(x*x*s.cos(2*x))
J=s.expand(A1*M2-A2*M1)
mu0=(13*L-8)/(144-54*L)
assert s.simplify(J.subs({eps:0,m:mu0}))==0
mu1=s.factor(-s.diff(J,eps).subs({eps:0,m:mu0})
              /s.diff(J,m).subs({eps:0,m:mu0}))
assert s.simplify((s.diff(J,eps)+s.diff(J,m)*mu1)
                  .subs({eps:0,m:mu0}))==0

# Source pole: cos(16x)*cos(cx) at high t, on-line cos(cx).
B1=pairing(s.cos(16*x)*s.cos(x))
B2=pairing(s.cos(16*x)*s.cos(2*x))
P=s.expand(B1*A2-B2*A1)
# Source combined profile 4 G(x) [A1*cos(2x)-A2*cos(x)].
K=s.expand(4*pairing((A1*s.cos(2*x)-A2*s.cos(x))*s.cos(4*x)))

def jet(expr):
    base=s.factor(expr.subs({eps:0,m:mu0}))
    linear=s.factor((s.diff(expr,eps)+s.diff(expr,m)*mu1)
                    .subs({eps:0,m:mu0}))
    return base,linear

p0,p1=jet(P)
k0,k1=jet(K)
assert s.simplify(p0-3*(2-L)/4)==0
assert s.simplify(k0-3*(L-2))==0
a,b=F(1,2),F(2,3)
at=lambda v,l:s.factor(v.subs(L,l))
constant=s.factor(at(p0,b)*at(k0,a)-at(p0,a)*at(k0,b))
linear=s.factor(at(p0,b)*at(k1,a)+at(p1,b)*at(k0,a)
                -at(p0,a)*at(k1,b)-at(p1,a)*at(k0,b))
assert constant==0
assert linear==F(120,13)
assert linear>0

print("PASS atomic high-pole determinant and exact J2-null mu0")
print("PASS moving mu1 preserves J2 to first order in bump second moment")
print("PASS selected smooth high-t q=4 constant 0; eps coefficient +120/13")
print("CONDITIONAL: remainder controlled by E[Y^4]+eps^2")
print("OPEN finite-t uniform positive-R selected W, actual zero signed payment, local slack")
