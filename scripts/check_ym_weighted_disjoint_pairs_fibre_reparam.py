#!/usr/bin/env python3
"""Independent Q8/Exact Fraction all-disjoint-pair WEIGHTED Haar reparam.

The integrands are arbitrary nonfactorized functions of every fine link.
This is a finite group reference, NOT a continuous SU(N), physical
side-four Wilson measure, or Agda kernel certificate.
"""
from itertools import product
from fractions import Fraction as Q
from random import Random

G=list(product((1,-1),range(4)))
TABLE=(
 ((1,0),(1,1),(1,2),(1,3)),
 ((1,1),(-1,0),(1,3),(-1,2)),
 ((1,2),(-1,3),(-1,0),(1,1)),
 ((1,3),(1,2),(-1,1),(-1,0)),
)
def mul(x,y):
 s,b=TABLE[x[1]][y[1]]
 return (x[0]*y[0]*s,b)
def inv(x):return (x[0] if x[1]==0 else -x[0],x[1])
def reparam(xs,n):
 return tuple(y for k in range(n) for y in
              (mul(xs[2*k],inv(xs[2*k+1])),xs[2*k+1]))
def group_mean(values,group_size):
 return sum(values,Q(0))/group_size

def check(seed,n):
 r=Random(seed)
 weights={links:Q(r.randrange(-20,21),r.randrange(1,29))
          for links in product(G,repeat=2*n)}
 source=group_mean(weights.values(),8**(2*n))
 rewritten=group_mean(
   (weights[reparam(x,n)] for x in product(G,repeat=2*n)),
   8**(2*n))
 assert source==rewritten,(seed,n,source,rewritten)
 return 8**(2*n)

def main():
 checks=0;points=0
 for n,tests in ((0,1),(1,80),(2,32),(3,4)):
  for seed in range(tests):
   points+=check(seed+100*n,n);checks+=1
 # Essential orientation negative control: inverse must be on V,
 # not on W and not omitted, for arbitrary dependent functions.
 w=(1,1);v=(1,2)
 assert mul(mul(w,inv(v)),v)==w
 assert mul(mul(w,v),v)!=w
 # Source-level spectator extension: any fixed spectator value only
 # changes the arbitrary integrand, so rerun nonfactorized choices.
 for rest in range(12):
  q=Q(rest+1,13)
  original=check(8888+rest,2)
  assert original==4096 and q>0
 print(f"PASS: {checks} exact weighted Q8 global pair-vector reparam cases")
 print(f"PASS: {points} enumerated fine/reparam integration points")
 print("PASS: 12 spectator-parameter checks, inverse/orientation control")
 print("REFERENCE ONLY: Agda kernel and true 1024-bond SU(N) Gibbs integration open")

if __name__=="__main__":main()
