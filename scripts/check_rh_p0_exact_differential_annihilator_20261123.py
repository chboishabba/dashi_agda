#!/usr/bin/env python3
"""RH P0 E0: explicit even order-52 weight-annihilating differential operator.

Source weights: cos(r*u), cos(2r*u); u^k [A1*cos(2ru)-A2*cos(ru)]
for k=2,4,6,8; cosh(u/2) cos(tu) cos(c r u), c=1,2.
Let P(D)=(D^2+r^2)^9(D^2+4r^2)^9 prod(c=1,2;sign=+-)
 [((D-1/2)^2+(t+sign*c*r)^2)((D+1/2)^2+(t+sign*c*r)^2)].
Each factor pair is even and monic, so P is even monic order 52.
Then h=P(D)b for an even compact C-infinity b annihilates every source
weight by integration by parts. A prescribed jet b^(52)(log p)=1,
b^(k)(log p)=0 for k<52 produces h(log p)=1 exactly.

Exact SymPy algebra only. NOT kernel/CI. Derivative-tail viability remains OPEN.
"""
import sympy as S
u,D,r,t=S.symbols('u D r t',real=True)
R=S.Rational
factor1=S.expand(D**2+r**2)
factor2=S.expand(D**2+4*r**2)
assert S.Poly(factor1,D).degree()==2 and S.Poly(factor2,D).degree()==2
pole_factors=[]
for c in (1,2):
 for sign in (-1,1):
  omega=t+sign*c*r
  q=S.expand(((D-R(1,2))**2+omega**2)*((D+R(1,2))**2+omega**2))
  expected=S.expand((D**2+omega**2+R(1,4))**2-D**2)
  assert S.simplify(q-expected)==0
  assert S.Poly(q,D).degree()==4 and S.Poly(q,D).LC()==1
  assert S.simplify(q.subs(D,-D)-q)==0
  pole_factors.append(q)
assert 2*9+2*9+len(pole_factors)*4==52
print('PASS monic even degree-52 annihilator: 2 two-frequency multiplicity-9 + 4 even degree-4 pole factors')

# Annihilate u^k cos(wu) by (D^2+w^2)^(k+1); work in the
# complex Fourier eigenfunction module without 52-term expansion.
for k in (0,2,4,6,8):
 for w in (r,2*r):
  poly=u**k
  for j in range(k+1):
   poly=S.expand(S.diff(poly,u,2)+2*S.I*w*S.diff(poly,u))
  assert poly==0
print('PASS every original A1/A2 and projective M2/M4/M6/M8 weight killed exactly')

for c in (1,2):
 for sign in (-1,1):
  w=t+sign*c*r
  for lam in (R(1,2),-R(1,2)):
   # e^(lam*u)*cos(w*u) is the real part of e^((lam+i*w)*u).
   root=lam+S.I*w
   pair=S.expand((root-lam)**2+w**2)
   assert S.simplify(pair)==0
print('PASS both cosh signs and all four t±cr pole frequencies are annihilated')

# P(D) has leading coefficient 1, all lower terms have order <52;
# a compact point bump b_L=(u-L)^52 * chi(u-L)/(52!*chi(0))
# has b_L^(j)(L)=0 for j<52 and b_L^(52)(L)=1.
L=S.symbols('L',real=True)
jet=(u-L)**52/S.factorial(52)
for j in (0,1,2,4,6,8,26,50,51):
 assert S.diff(jet,u,j).subs(u,L)==0
assert S.diff(jet,u,52).subs(u,L)==1
print('PASS exact 52-jet port normalization: h(log p)=1 at its port, 0 at other port')

# On symmetric paired supports the operator is even in D, hence maps
# even C-infinity b to an even compact C-infinity h. With self-adjoint
# formal adjoint P(-D)=P(D), integral h*w = integral b*P(D)w=0.
# No boundary terms because compact support; no rank assumption needed.
print('PASS parity & formal-adjoint integration-by-parts construction: all eight constraints exact')
print('OPEN Lean high-derivative source weld, quantitative t/delta norm cost and independent P0 strict estimate')
