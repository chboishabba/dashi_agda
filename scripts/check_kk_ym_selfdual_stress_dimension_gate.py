#!/usr/bin/env python3
"""Exact 4D-Euclidean / 5D-Lorentzian YM stress separation.

Classical: self-duality, Bianchi, stress tensor, standard Einstein-YM.
Recent literature: B. Diez, "Gravitational Cheshire effect from
Yang-Mills instantons", arXiv:2610.24127 (16 Oct 2026), studies Euclidean
four-dimensional Einstein-YM. Not evidence of 5D Lorentzian backreaction
cancellation. Existing DASHI physical YM stress/OS owners remain unchanged.
Current new contribution: 3-colour arbitrary self-dual tensor symbolic audit.
No claim that the selected original Balaban source admits this 5D solution.
"""
import sympy as s

c=s.Matrix(3,3,lambda a,i:s.Symbol(f"c{a}{i}",real=True))
F=[]
# Oriented Euclidean 4D self-dual 2-form basis:
# (e12+e34, e13-e24, e14+e23).
for a in range(3):
    f=s.zeros(4,4)
    p,q,t=c.row(a)
    for i,j,v in [(0,1,p),(2,3,p),(0,2,q),(1,3,-q),
                  (0,3,t),(1,2,t)]:
        f[i,j]=v
        f[j,i]=-v
    F.append(f)
quad=s.expand(sum(sum(f[i,j]**2 for i in range(4) for j in range(4))
                  for f in F))
E=s.expand(quad/4)
T4=s.Matrix(4,4,lambda i,j:s.expand(
    sum(sum(f[i,k]*f[j,k] for k in range(4)) for f in F)
    -s.KroneckerDelta(i,j)*quad/4))
assert T4==s.zeros(4)
assert s.expand(E-sum(c[a,i]**2 for a in range(3)
                        for i in range(3)))==0
assert E!=0
# For static 5D Lorentzian -++++, F0i=0, T00= +FijFij/(4g5^2).
print("PASS: arbitrary three-colour 4D self-dual YM has T_Euclidean=0")
print("PASS: static 4+1 YM T00=FijFij/(4g5^2), generically positive")
print("LIMIT: unit gauge-coupling normalization, pointwise tensor identity")
print("NO CLAIM: complete coupled 5D Einstein-YM without backreaction")
