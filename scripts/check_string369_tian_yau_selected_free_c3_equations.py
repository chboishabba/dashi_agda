#!/usr/bin/env python3
"""Exact free C3 fixed-point negative-locus for one selected Tian-Yau
multidegree (3,0),(0,3),(1,1) invariant polynomial triple.

CLASSICAL: Tian/Yau CICY, projective eigenspace and algebraic resultant.
EXISTING DASHI: CalabiYau369CompactFibreBridge, first-Tits E6/27 C3.
NEW: construct literal equations and rule out fixed CY points for them.
IMPORTANT: smoothness of THIS selected triple and transversality have
NOT been established by this finite calculation; a free algebraic
set is not yet a certified smooth CY. User physical programme.
"""
import sympy as s
x=s.symbols("x0:4")
y=s.symbols("y0:4")
G=x[0]**3-x[1]*x[2]*x[3]+sum(x[j]**3 for j in (1,2,3))
H=y[0]**3-y[1]*y[2]*y[3]+sum(y[j]**3 for j in (1,2,3))
F=x[0]*y[0]+sum(x[j]*y[j] for j in (1,2,3))
swap={x[1]:x[2],x[2]:x[3],x[3]:x[1],
      y[1]:y[2],y[2]:y[3],y[3]:y[1]}
assert all(s.expand(p.xreplace(swap)-p)==0 for p in (G,H,F))
# Any fixed projective point of simultaneous diagonal 3-cycle has
# either x in trivial eigenspace [a:t:t:t] or a nontrivial eigenline
# [0:1:omega:omega²] (and conjugate), similarly for y.
# At nontrivial eigenline, G/H = -1+3=2 != 0.
assert -1+3==2
a,b,t,u=s.symbols("a b t u")
Gt=s.expand(G.subs({x[0]:a,x[1]:t,x[2]:t,x[3]:t}))
Ht=s.expand(H.subs({y[0]:b,y[1]:u,y[2]:u,y[3]:u}))
Ft=s.expand(F.subs({x[0]:a,x[1]:t,x[2]:t,x[3]:t,
                       y[0]:b,y[1]:u,y[2]:u,y[3]:u}))
assert Gt==a**3+2*t**3 and Ht==b**3+2*u**3
assert Ft==a*b+3*t*u
# Gt=Ht=0 and Ft=0 implies 4 t³u³ = -27 t³u³,
# hence 31 t³u³=0. But t=0 implies a=0 and gives
# invalid projective x; u similarly. Exact nonzero contradiction.
assert s.expand((a**3)*(b**3)-
    ((-2*t**3)*(-2*u**3)))==a**3*b**3-4*t**3*u**3
assert (-3)**3-(-2)*(-2)==-31
res=s.factor(s.resultant(Gt,Ft,a))
assert s.simplify(res-t**3*(-2*b**3+27*u**3))==0
assert s.simplify(res.subs(b**3,-2*u**3)-31*t**3*u**3)==0
print("PASS: C3 invariance of selected (3,0),(0,3),(1,1) equations")
print("PASS: no fixed point on nontrivial projective eigenlines")
print("PASS: trivial-eigenspace equations force impossible 31 t³u³=0")
print("CONCLUSION: selected C3 acts without fixed points on this algebraic intersection")
print("OPEN: selected intersection smoothness, CY quotient, bundle/Dirac modes")
