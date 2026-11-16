#!/usr/bin/env python3
"""RH R2 source-faithful projective-profile L1 transport; NOT a proof of RH.

Source: dashi_lean4/Synthesis/RiemannProjectiveCircularHyperbolicDuality.lean
and RiemannProjectiveQuarticFourWindow*.lean on agent/rh-postmerge-maxcut-20261007.
Attribution: original projective definitions and smooth windows are from those
Lean modules; this file derives independent symbolic envelope checks.
"""
import sympy as s
from math import comb

R,B0=s.symbols("R B0",positive=True)
lam,mu=s.symbols("lam mu",real=True)
B=s.symbols("B1:5",nonnegative=True)
u,A1,A2=s.symbols("u A1 A2",real=True)
H=4*(A1*s.cos(2*u)-A2*s.cos(u))
for d in range(5):
    rhs=4*(A1*2**d*s.cos(2*u+d*s.pi/2)-A2*s.cos(u+d*s.pi/2))
    assert s.trigsimp(s.diff(H,u,d)-rhs)==0
Q0=2+s.Abs(lam)+s.Abs(mu)
Q=[Q0]+[Q0*B[j-1]/(B0*R**j) for j in range(1,5)]
M=[]
for j in range(5):
    mj=4*Q0*sum(comb(j,k)*(2**(j-k)+1)*Q[k] for k in range(j+1))
    M.append(mj)
    print("P%d_L1_upper ="%j,s.factor(mj))
assert s.expand(M[0]-8*Q0**2)==0
assert s.expand(M[1]-4*Q0*(3*Q0+2*Q[1]))==0
# Exact binomial expansion of fourth-order Fourier-IBP norm envelope.
a=s.symbols("a",nonnegative=True)
D=sum(comb(4,j)*a**(4-j)*M[j] for j in range(5))
assert s.expand(D.subs(a,0)-M[4])==0
print("IBP_fourth_norm =",s.factor(D))
print("PASS: no derivative of g occurs in projective multiplier (p=0)")
print("OPEN: explicit Mathlib bump B1..B4, selected R/mu/pole weights,")
print("      literal finite signed margin, correct cofinal quantifiers, native proof")
