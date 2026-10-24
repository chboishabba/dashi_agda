#!/usr/bin/env python3
"""Exact source #1106 V6 restricted to orbifold-even Chi E21 EW Higgs path.

Phi=E32, Chi=E33+t E21. Actual first-Tits source six-invariant
quartic gives V6(t)=3t²+t⁴; it DOES NOT spontaneously break EW.
An S1/Z2 fixed-plane term -mu² Tr(P2L Chi P2R Chi†)
+lambda [Tr(P2L Chi P2R Chi†)]² is invariant under the REDUCED
orbifold boundary SU2LxU1LxSU2RxU1R, not under full bulk SU3³.
It yields one-dimensional path V=(3-mu²)t²+(1+lambda)t⁴.
For mu²>3, lambda>-1 this slice has a nonzero local minimum,
t²=(mu²-3)/[2(1+lambda)] and Hessian 4(mu²-3)>0.
NOT a critical point/full Hessian in the full 36-real source
field theory nor a measured SM electroweak vacuum.
"""
import sympy as s
def E(i,j):
    M=s.zeros(3);M[i,j]=1;return M
phi=E(2,1)
t,mu2,lam=s.symbols("t mu2 lambdaB",real=True)
chi=E(2,2)+t*E(1,0)
def tr(M):return sum(M[k,k] for k in range(M.rows))
def sourceV6(a,b):
    na=tr(a.H*a); nb=tr(b.H*b)
    return s.expand((na-1)**2+(nb-1)**2
       +na**2-tr((a.H*a)**2)+nb**2-tr((b.H*b)**2)
       +tr(a.H*a*b.H*b)+na*nb-tr(a*a.H*b*b.H))
v=sourceV6(phi,chi)
assert s.expand(v-(3*t*t+t**4))==0
P2=s.diag(1,1,0)
boundary_norm=tr(P2*chi*P2*chi.H)
assert s.expand(boundary_norm-t*t)==0
vnew=s.expand(v-mu2*boundary_norm+lam*boundary_norm**2)
assert s.expand(vnew-((3-mu2)*t*t+(1+lam)*t**4))==0
tsquared=(mu2-3)/(2*(1+lam))
assert s.simplify(s.cancel(s.diff(vnew,t)/t).subs(t*t,tsquared))==0
assert s.simplify(s.diff(vnew,t,2).subs(t*t,tsquared)
                  -4*(mu2-3))==0
# Illustrative relative EW vs E6 vev; exact normalization is NOT
# physical until the source kinetic term/couplings are supplied.
ratio=s.Rational(246,10000)
delta=4*ratio**2
assert delta==s.Rational(15129,6250000)
print("PASS exact E6 V6 source restriction =",s.factor(v))
print("PASS orbifold boundary even-2x2 norm =",boundary_norm)
print("PASS restricted source with boundary mass =",s.factor(vnew))
print("illustrative mu²-3 at vE6=10TeV,vEW=246GeV,lambdaB=1:",delta)
print("OPEN complete 36-real scalar Hessian, source dimensions, boundary quantum action, radion/CS, real EW phenomenology")
