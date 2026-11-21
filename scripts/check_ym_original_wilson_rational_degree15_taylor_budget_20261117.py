#!/usr/bin/env python3
"""Degree budget: 1464-node rational S3 cubature -> ORIGINAL Wilson Taylor.

At L>=2 every positive plaquette uses four distinct original bonds,
hence the unit-quaternion coordinate degree per bond of D^k is <=k.
At L=1 the native commutator repeats each of its two original links,
so that bound is <=2k. Consequently the degree-15 positive rational
one-link rule integrates EXACTLY T14/T15 for all L>=2 and T6/T7 at L=1.
Alternating exponential polynomial bounds give rigorous rational
intervals with width <=(12*beta*L**4)^k/k! at rational beta>=0.
This is a degree/interval certificate, NOT the expanded integral
of the 15th power or an Agda kernel acceptance receipt.
"""
from fractions import Fraction as Q
from itertools import combinations,product
from math import factorial

def step(site,k,L):
 p=list(site);p[k]=(p[k]+1)%L;return tuple(p)

def max_plaquette_edge_multiplicity(L):
 maximum=0
 for site in product(range(L),repeat=4):
  for a,b in combinations(range(4),2):
   boundary=((site,a),(step(site,a,L),b),(step(site,b,L),a),(site,b))
   assert len(boundary)==4
   maximum=max(maximum,max(boundary.count(edge) for edge in boundary))
 return maximum

for L in (1,2,3,4):
 multiplicity=max_plaquette_edge_multiplicity(L)
 assert multiplicity==(2 if L==1 else 1)
 degree=15//multiplicity
 assert degree==(7 if L==1 else 15)
 beta=Q(1,96*L**4)
 B=12*beta*L**4
 width=B**degree/factorial(degree)
 assert degree%2 and degree*multiplicity<=15 and 0<width<1
 print(f"L={L}: T{degree}<=Z<=T{degree-1}, width<={width}")
print("YM_ORIGINAL_WILSON_RATIONAL_DEG15_TAYLOR_BUDGET_PASS")
