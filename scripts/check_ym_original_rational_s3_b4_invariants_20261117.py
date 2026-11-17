#!/usr/bin/env python3
"""Independent symbolic validation of the original rational SU2
hyperoctahedral generator Agda owner. Sign flips + adjacent swaps
preserve the original quaternion norm and all e2,e3,e4 invariants.
This is a symbolic reference, not Agda kernel acceptance.
"""
import sympy as S
from itertools import combinations
x=S.symbols('a b c d',real=True)
G=[x,(-x[0],x[1],x[2],x[3]),(x[0],-x[1],x[2],x[3]),
   (x[0],x[1],-x[2],x[3]),(x[0],x[1],x[2],-x[3]),
   (x[1],x[0],x[2],x[3]),(x[0],x[2],x[1],x[3]),
   (x[0],x[1],x[3],x[2])]
def invs(t):
 y=[v*v for v in t]
 return(sum(y),
        sum(y[i]*y[j] for i,j in combinations(range(4),2)),
        sum(y[i]*y[j]*y[k] for i,j,k in combinations(range(4),3)),
        S.prod(y))
checks=0
for g in G:
 for actual,expected in zip(invs(g),invs(x)):
  assert S.expand(actual-expected)==0
  checks+=1
print("YM_ORIGINAL_S3_B4_GENERATOR_INVARIANT_PASS",checks)
