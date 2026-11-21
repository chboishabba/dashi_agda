#!/usr/bin/env python3
"""Exact reduction of degree-15 rational S3 cubature to 11 invariants.

This verifier checks the genuine 11-orbit rational design against
11 independently expanded Pochhammer invariant moments. It then
reduces EVERY distinct signed-permutation orbit of degree <=15 via
SymPy symmetric polynomial elimination with e1=sum qi²=1.
Source Agda owner: YMClayRationalS3DegreeFifteenInvariantCertificateExact.
No numeric optimizer, floats, square roots or pi.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
import runpy
import sympy as S

src=runpy.run_path(str(Path(__file__).with_name(
    "check_ym_s3_exact_rational_orbit_degree15_20261117.py")))
CERT=src["CERT"]
H=src["H"]
EXPS=[(a,b,c) for a in range(4) for b in range(3) for c in range(2)
      if 2*a+3*b+4*c<=7]
assert len(EXPS)==11

def orbit_inv(q):
 y=[v*v for v in q]
 return (sum((y[i]*y[j] for i,j in combinations(range(4),2)),F(0)),
         sum((y[i]*y[j]*y[k] for i,j,k in combinations(range(4),3)),F(0)),
         y[0]*y[1]*y[2]*y[3])

x=S.symbols("x:4")
e2=sum((x[i]*x[j] for i,j in combinations(range(4),2)),S.S.Zero)
e3=sum((x[i]*x[j]*x[k] for i,j,k in combinations(range(4),3)),S.S.Zero)
e4=S.prod(x)
for a,b,c in EXPS:
 lhs=sum((w*orbit_inv(q)[0]**a*orbit_inv(q)[1]**b*orbit_inv(q)[2]**c
          for q,w in CERT),F(0))
 expansion=S.Poly(S.expand(e2**a*e3**b*e4**c),*x)
 rhs=sum((F(int(coeff))*H(tuple(2*t for t in power))
          for power,coeff in expansion.terms()),F(0))
 assert lhs==rhs,(a,b,c,lhs,rhs)
 print(f"invariant {(a,b,c)} = {rhs}")

seen=set()
for degree in range(8):
 for a in range(degree+1):
  for b in range(degree-a+1):
   for c in range(degree-a-b+1):
    d=degree-a-b-c
    ex=(a,b,c,d)
    key=tuple(sorted(ex))
    if key in seen:continue
    seen.add(key)
    f=sum((S.prod(x[i]**n for i,n in enumerate(p))
           for p in set(permutations(ex))),S.S.Zero)
    expression,remainder,formal=S.symmetrize(f,x,formal=True)
    assert remainder==0
    E1,E2,E3,E4=[symbol for symbol,_ in formal]
    polynomial=S.Poly(S.expand(expression.subs(E1,1)),E2,E3,E4)
    for powers,coeff in polynomial.terms():
     assert powers in EXPS,(key,powers)
print("YM_S3_DEG15_ELEVEN_INVARIANTS_PASS:",
      len(EXPS),"independent moment constraints,",
      len(seen),"complete symmetric orbit classes")
