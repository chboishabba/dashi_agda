#!/usr/bin/env python3
"""Exact full Monster Vnatural weight2 order27 spectral multiplicities and
balanced 3x3x3 cube CHART. Provenance:
ATLAS 27A/B power to 9B and 3B;
McKay-Thompson q coefficients 27AB:3, 9B:0, 3B:54;
FLM grade2 dimension 196884, rational 196883 constituent.
This is a cyclic spectral chart, NOT cube geometry or VOA fusion.
"""
from itertools import product
from collections import Counter
from math import gcd

DIM=196884
CHAR={0:196884,1:3,3:0,9:54}
CONDUCTOR_COUNTS={1:7298,3:7295,9:7296,27:7290}
def mobius(n):
 fac=[];d=2
 while d*d<=n:
  if n%d==0:
   n//=d;fac.append(d)
   if n%d==0:return 0
  else:d+=1
 if n>1:fac.append(n)
 return (-1)**len(fac)
def phi(n):return sum(gcd(k,n)==1 for k in range(n))
def ramanujan(d,j):
 t=d//gcd(d,j)
 return mobius(t)*phi(d)//phi(t)
for j,c in CHAR.items():
 assert sum(CONDUCTOR_COUNTS[d]*ramanujan(d,j)
            for d in CONDUCTOR_COUNTS)==c,(j,c)

CUBE=tuple(product((-1,0,1),repeat=3))
assert len(CUBE)==27
def label(p):return sum(p[i]*3**i for i in range(3))%27
def order_of_eigen(k):return 27//gcd(k,27)
rank={p:CONDUCTOR_COUNTS[order_of_eigen(label(p))] for p in CUBE}
assert Counter(rank.values())=={7290:18,7296:6,7295:2,7298:1}
assert sum(rank.values())==196884
assert rank[(0,0,0)]==7298
assert {p for p in CUBE if rank[p]==7295}=={(0,0,1),(0,0,-1)}
assert all(rank[p]==7296 for p in CUBE if p[0]==0 and p[1]!=0)
assert all(rank[p]==7290 for p in CUBE if p[0]!=0)

# Braid M on a chosen spatial xy sheet and cyclic charge operator are
# INDEPENDENT; M permutes charge labels, it is not an onsite C27 symmetry.
def res(z):return ((z+1)%3)-1
def M(p):return res(p[0]+p[1]),res(p[0]-p[1]),p[2]
migrating=Counter((rank[p],rank[M(p)]) for p in CUBE)
assert sum(migrating.values())==27

# Each native nearest-neighbour edge changes a different cyclotomic
# charge exponent, with 3 axes matching increments 1/3/9, NOT
# an M-invariant graph or a cyclic 27 spatial rotation.
E=set()
for p in CUBE:
 for i in range(3):
  q=list(p);q[i]+=1
  if q[i]<=1:E.add((p,tuple(q),i))
assert len(E)==54
by_axis=Counter(i for p,q,i in E)
assert by_axis=={0:18,1:18,2:18}
assert all((label(q)-label(p))%27==3**i for p,q,i in E)
assert all(label(p)!=label(q) for p,q,i in E)

# Universal no-go: if each cube vertex is a DIFFERENT g-eigencharge
# fibre, a plain nonzero hopping operator from p to q cannot commute
# with g because eigenphases differ. Every cube grid edge violates it.
assert all(gcd(27,(label(q)-label(p))%27)!=27 for p,q,i in E)
assert {i:gcd(27,3**i) for i in range(3)}=={0:1,1:3,2:9}

print('PASS exact Monster McKay-Thompson char checks: T_27=3 T_9B=0 T_3B=54')
print('PASS C27 eigenspace multiplicities: phi1:7298 phi3:7295 phi9:7296 phi27:7290')
print('PASS spatial cube chart 27 sites; fibre dimensions',sorted(Counter(rank.values()).items()))
print('PASS cube axis edges 18 each with cyclic-charge shifts +1,+3,+9')
print('PASS distinct-charge intersite hopping impossible under strictly preserved onsite g')
print('GATE physically gauged charged links or uniform full-VOA onsite copies needed for local coupling')
