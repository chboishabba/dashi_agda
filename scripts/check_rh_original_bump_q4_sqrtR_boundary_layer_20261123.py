#!/usr/bin/env python3
"""Original RH selected smooth J2 branch: q=4 boundary-layer source Taylor.

Sources: original Lean FourWindow/PoleSameObject/SignedPoleTarget, fixed
even compact Mathlib bump (NOT Gaussian) with m2=E[Z²]∈[1/24,1],
and explicit original R=1e-10 q4 source majorants.
Exact local symbolic leading coefficient, not a Lean kernel proof or
a finite-t q-neighborhood sign receipt; no actual zeta zeros.
"""
import sympy as s
Q=s.Rational
lam,mu,e,q=s.symbols('lam mu e q',real=True)
centres=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
weights=(s.Integer(1),-1,lam,mu)
def cf(k):return s.expand(sum(w*s.cos(k*c) for w,c in zip(weights,centres)))
def sf(k):return s.expand(sum(w*c*s.sin(k*c) for w,c in zip(weights,centres)))
def c2(k):return s.expand(sum(w*c*c*s.cos(k*c) for w,c in zip(weights,centres)))
def A(k):return s.expand((1-e*k*k)*cf(k))
def M(k):return s.expand((1-e*k*k)*c2(k)+2*e*cf(k)-4*e*k*sf(k))
J=A(1)*M(2)-A(2)*M(1)
mu0=(13*lam-8)/(144-54*lam)
mu1=s.factor((-s.diff(J,e)/s.diff(J,mu)).subs({e:0,mu:mu0}))
P=(A(15)+A(17))*A(2)/2-(A(14)+A(18))*A(1)/2
def Qp(n):return 2*(A(1)*(A(n-2)+A(n+2))-A(2)*(A(n-1)+A(n+1)))
def first_two(expr,l):
  u=mu0.subs(lam,l)+mu1.subs(lam,l)*e
  z=s.expand(expr.subs({lam:l,mu:u}))
  return s.expand(z.subs(e,0)),s.expand(s.diff(z,e).subs(e,0))
hP0,hP1=first_two(P,Q(1,2));tP0,tP1=first_two(P,Q(2,3))
hQ0,hQ1=first_two(Qp(q),Q(1,2));tQ0,tQ1=first_two(Qp(q),Q(2,3))
K0=tP0*hQ0-hP0*tQ0
K1=tP0*hQ1+tP1*hQ0-hP0*tQ1-hP1*tQ0
assert s.simplify(Qp(0))==0 and s.simplify(K0.subs(q,0))==0
assert s.simplify(s.trigsimp(K0.subs(q,4)))==0
assert s.simplify(s.trigsimp(K1.subs(q,4))-Q(120,13))==0
v=s.simplify(s.trigsimp(s.diff(K1,q).subs(q,4)))
assert s.simplify(v+200*s.sqrt(3)*s.pi/117+Q(10,13)-764*s.pi/351)==0
x,m=s.symbols('x m',positive=True)
a=5*s.pi**4/1404
lead=60*m/13-a*x**4
assert s.simplify(s.solve(lead,x**4)[0]-1296*m/s.pi**4)==0
lo=s.simplify(lead.subs({m:Q(1,24),x:Q(1,2)}))
hi=s.simplify(lead.subs({m:1,x:2}))
assert lo==Q(5,26)-5*s.pi**4/22464
assert s.simplify(hi-Q(20,351)*(81-s.pi**4))==0
assert Q(5,26)-5*Q(22,7)**4/22464>0
assert (Q(20,351)*(81-s.pi**4))<0 and 3<s.pi
assert 6/s.pi<2
assert 6/s.pi*Q(1,24)**Q(1,4)>Q(1,2)
print("PASS original J2-selected high-pole K0(0)=K0(4)=0 and K1(4)=120/13")
print("PASS exact K1'(4)",v)
print("PASS sqrt(R) boundary: 60 m2/13 -5*pi^4 x^4/1404")
print("PASS x=1/2 positive uniformly m2>=1/24; x=2 negative m2<=1 with pi>3")
print("PASS asymptotic signed Fourier zeros q=4±6*m2^(1/4)/pi*sqrt(R)+o(sqrtR)")
print("OPEN explicit fixed-R adjacent sign theorem, finite t, ζ zeros/μ/FarExact")
