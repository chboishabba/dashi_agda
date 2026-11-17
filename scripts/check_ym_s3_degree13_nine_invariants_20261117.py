#!/usr/bin/env python3
"""Compact degree-13 exact positive rational S3 cubature certificate.

Signed coordinate changes remove every odd-coordinate monomial; permutation
averaging reduces even monomials to symmetric polynomials in yi=qi^2.
On S3 e1=sum yi=1. The nine generators of symmetric degree <=6 are:
1,e2,e3,e4,e2**2,e2*e3,e2**3,e3**2,e2*e4.
Their exact rational moments and orbit averages suffice for degree <=13.
This checker *also* invokes the independently established 2380-monomial
rational-orbit certificate. SymPy is only used for exact symmetric
polynomial reduction, not floating point root/weight fitting.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
import runpy
import sympy as s

source = runpy.run_path(str(Path(__file__).parent /
                            "check_ym_s3_exact_rational_orbit_designs_20261117.py"))
entries=source["C"][13]
basis=(
 ("1",(0,0,0),F(1)),
 ("e2",(1,0,0),F(1,4)),
 ("e3",(0,1,0),F(1,48)),
 ("e4",(0,0,1),F(1,1920)),
 ("e2^2",(2,0,0),F(11,160)),
 ("e2*e3",(1,1,0),F(1,160)),
 ("e2^3",(3,0,0),F(89,4480)),
 ("e3^2",(0,2,0),F(3,4480)),
 ("e2*e4",(1,0,1),F(3,17920)),
)
def inv(q):
 y=[x*x for x in q]
 return (
  sum((y[i]*y[j] for i,j in combinations(range(4),2)),F(0)),
  sum((y[i]*y[j]*y[k] for i,j,k in combinations(range(4),3)),F(0)),
  y[0]*y[1]*y[2]*y[3])
assert len(entries)==9 and sum(w for _,w in entries)==1
assert all(sum(x*x for x in q)==1 and w>0 for q,w in entries)
for name,(a,b,c),expected in basis:
 value=sum((w*inv(q)[0]**a*inv(q)[1]**b*inv(q)[2]**c
            for q,w in entries),F(0))
 assert value==expected,(name,value,expected)
 print(name, "=", value)

y=s.symbols("y0:4")
# Check the finite-dimensional invariant-theory reduction for every orbit
# monomial of total y-degree <=6 (corresponding to q-degree <=12).
count=0
for d in range(7):
 for a in range(d+1):
  for b in range(d-a+1):
   for c in range(d-a-b+1):
    e=d-a-b-c
    f=sum((s.prod(y[i]**n for i,n in enumerate(ex))
           for ex in set(permutations((a,b,c,e)))),s.S.Zero)
    expression,remainder,elementaries=s.symmetrize(f,y,formal=True)
    assert remainder==0
    e1,e2,e3,e4=(sym for sym,_ in elementaries)
    # Reduce e1 to 1 on q0²+q1²+q2²+q3²=1.
    reduced=s.Poly(s.expand(expression.subs(e1,1)),e2,e3,e4)
    for (u,v,w),coeff in reduced.terms():
     assert 2*u+3*v+4*w<=6
     assert (u,v,w) in {powers for _,powers,_ in basis}
    count+=1
print("YM_S3_DEG13_NINE_INVARIANT_CERTIFICATE_PASS",
      len(basis), "moment constraints,",count,"symmetric orbit monomials")
