#!/usr/bin/env python3
"""Exact optical C3 invariants and NS signed-work centering for three channels.
Physical YM and optical channel representations are NOT assumed identical.
"""
import sympy as s
a,b,c,r0,r1,r2=s.symbols("a b c r0 r1 r2",real=True)
def rotate(x): return (x[2],x[0],x[1])
x=(a,b,c)
assert rotate(rotate(rotate(x)))==x
assert s.expand(sum(rotate(x))-sum(x))==0
assert s.expand(sum(rotate(x))**2-sum(x)**2)==0
def cross_terms(ch):return [2*ch[0]*ch[1],2*ch[1]*ch[2],2*ch[2]*ch[0]]
v=cross_terms(x)
assert all(s.expand(i-j)==0 for i,j in zip(cross_terms(rotate(x)),rotate(v)))
R=[r0,r1,r2]
lhs=s.expand(-3*sum(R[i]*v[i] for i in range(3))+sum(R)*sum(v))
rhs=-sum((R[i]-R[j])*(v[i]-v[j]) for i in range(3) for j in range(i+1,3))
assert s.simplify(lhs-rhs)==0
assert s.expand(sum(x)**2 - sum(z*z for z in x) - sum(v))==0
print("PASS 369 C3 cubic symmetry and optical intensity invariance")
print("PASS cyclic covariance of amplitude-generated signed interference cross terms")
print("PASS NS ABCD division-free signed rate covariance identity on actual optical cross terms")
print("SCOPE no physical identification of Yang-Mills/NS and diamond photon pathways")
