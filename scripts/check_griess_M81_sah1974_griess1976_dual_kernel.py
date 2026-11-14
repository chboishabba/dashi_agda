#!/usr/bin/env python3
"""Exact source M81 dual-character-kernel conjugation certificate.

Original priority: Chih-Han Sah, J Algebra 29 (1974) 255-302 (earlier
cohomology result acknowledged by Griess); R. L. Griess Jr.,
Pacific J Math 63 (1976) 405-409, H^2(SL3(3),F3^3)=0 and splitting;
R. L. Griess Jr., J Algebra 131 (1990) 281-293 (THIS source g/M81).
Actual lifts/character shifts reuse Lean #52/Agda #1239 definitions.
Natural and dual SL3 modules are distinct but are related by outer
automorphism M->M^-T. Finite exact check is not a new proof of H^2,
nor a group-presentation section, Lean/Agda kernel or physical action.
"""
from itertools import product
V=tuple(product(range(3),repeat=3))
M=tuple(product(V,range(3)))
def sh(x,i,j):
 y=list(x);y[i]=(y[i]+y[j])%3;return tuple(y)
def corr(x,i,j):
 a,b,c=x
 return {(0,1):c*(1-b*b),(0,2):0,(1,0):c*(1-a*a),
         (1,2):a*(c*c-1),(2,0):0,(2,1):a*(b*b-1)}[i,j]%3
def lifted(a,i,j):
 x,k=a;return (sh(x,i,j),(k+corr(x,i,j))%3)
def kernel_shift(a,lam):
 x,k=a;return (x,(k+sum(lam[t]*x[t] for t in range(3)))%3)
def dual(lam,i,j):
 v=list(lam);v[j]=(v[j]-v[i])%3;return tuple(v)
for i,j in ((a,b) for a in range(3) for b in range(3) if a!=b):
 for lam,a in product(V,M):
  inv=lifted(lifted(a,i,j),i,j)
  left=lifted(kernel_shift(inv,lam),i,j)
  right=kernel_shift(a,dual(lam,i,j))
  assert left==right,(i,j,lam,a)
 # On all x,lambda the natural/dual character pairing is unchanged.
 for x,lam in product(V,repeat=2):
  assert sum(dual(lam,i,j)[k]*sh(x,i,j)[k] for k in range(3))%3==sum(lam[k]*x[k] for k in range(3))%3
print('PASS 13122 actual source six-shear × 27 characters × 81 M81 states conjugation laws')
print('PASS dual lambda action: lambda_j <- lambda_j - lambda_i; natural-dual pairing invariant')
print('PRIOR: Sah 1974/Griess 1976 H2 vanishing allows abstract split when actual extension hypotheses paid')
print('UNPAID: explicit same-source complement/group presentation, Lean/Agda kernel, physical/Monster actor')
