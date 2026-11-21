#!/usr/bin/env python3
"""Exact degree-15 rational positive S3 cubature: all 3876 monomials.

A numerical LP was used ONLY to discover the 11 candidate orbits.
The fixed rational total orbit weights were reconstructed from
an exact Q-linear solve. This executable verifies all weights, nodes
and complete monomial moments using fractions alone. No optimizer,
floats, pi, square roots or Haar oracle is needed to verify results.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import comb,prod

def p(*x):return tuple(Q(a) for a in x)
CERT=(
 (p(0,0,0,1),Q(5885276409378220035186191,392284006841077089848524800)),
 (p(0,Q(1,19),Q(6,19),Q(18,19)),Q(824693560522052736085185726477137,10149171824992346468561033625600000)),
 (p(0,Q(1,17),Q(12,17),Q(12,17)),Q(35494525410219178540065425306543,730913368646465860733017620480000)),
 (p(0,Q(2,11),Q(6,11),Q(9,11)),Q(471062302279446199657259685673,5242340818694393837066649600000)),
 (p(0,Q(2,7),Q(3,7),Q(6,7)),Q(9885750716129338579831646703499,88768266690895158617151897600000)),
 (p(0,Q(1,3),Q(2,3),Q(2,3)),Q(41184780746981187413434527,937511542031411182567424000)),
 (p(0,Q(6,11),Q(6,11),Q(7,11)),Q(40400171940295056739147947380699,433937435931111457206986342400000)),
 (p(Q(1,10),Q(3,10),Q(3,10),Q(9,10)),Q(8757912318951982421875,80448868590455262566592)),
 (p(Q(1,5),Q(2,5),Q(2,5),Q(4,5)),Q(2313779947035071669921875,21696695687012658796560384)),
 (p(Q(2,7),Q(2,7),Q(4,7),Q(5,7)),Q(14522081148341910799643057,55348713487277190807552000)),
 (p(Q(1,2),Q(1,2),Q(1,2),Q(1,2)),Q(839369233794076039,21497746937751927360)),
)
assert sum(w for q,w in CERT)==1
assert all(sum(v*v for v in q)==1 and w>0 for q,w in CERT)
perms={q:tuple(set(permutations(q))) for q,w in CERT}
def orbital(q,ex):
 if any(e%2 for e in ex):return Q(0)
 return sum((prod(a**n for a,n in zip(pt,ex)) for pt in perms[q]),Q(0))/len(perms[q])
def H(ex):
 if any(k%2 for k in ex):return Q(0)
 v=Q(1)
 for k in ex:
  for j in range(k//2):v*=Q(2*j+1,2)
 for j in range(sum(ex)//2):v/=j+2
 return v
count=0
for a in range(16):
 for b in range(16-a):
  for c in range(16-a-b):
   for d in range(16-a-b-c):
    e=(a,b,c,d)
    actual=sum((w*orbital(q,e) for q,w in CERT),Q(0))
    assert actual==H(e),(e,actual,H(e))
    count+=1
nodes=sum(len(perms[q])*2**sum(x!=0 for x in q) for q,w in CERT)
assert count==comb(19,4)==3876 and nodes==1464
print(f"YM_S3_D15_EXACT_POSITIVE_RATIONAL_ORBITS_PASS {count}/{count} monomials, {len(CERT)} orbits, {nodes} nodes")
