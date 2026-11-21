#!/usr/bin/env python3
"""Standalone exact rational S3 designs through degree 13.

No float/LP/root/angle dependency in verification. Nodes are complete
signed-permutation orbits of rational unit quaternions; each orbit has
positive rational total mass distributed uniformly. Check every
monomial in each complete degree basis against Pochhammer moments.
Attribution: Pizzetti/Folland, rational stereographic construction,
Wilson/Balaban original SU2, Bishop/Bridges.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import comb,prod

def p(*args):return tuple(Q(v) for v in args)
AX=p(1,0,0,0);HALF=p(Q(1,2),Q(1,2),Q(1,2),Q(1,2))
THIRD=p(Q(-1,3),Q(2,3),Q(2,3),0)
FA=p(0,Q(4,5),Q(3,5),0);FB=p(Q(-1,5),Q(4,5),Q(2,5),Q(2,5))
SIX=p(Q(-1,6),Q(5,6),Q(1,2),Q(1,6))
S7A=p(Q(3,7),Q(6,7),Q(2,7),0)
S7B=p(Q(1,7),Q(4,7),Q(4,7),Q(4,7))
S7C=p(Q(-2,7),Q(5,7),Q(4,7),Q(2,7))
NINE=p(Q(1,9),Q(8,9),Q(4,9),0)
TEN=p(Q(-1,10),Q(9,10),Q(3,10),Q(3,10))
C={
7:((AX,Q(167,960)),(HALF,Q(1,15)),(THIRD,Q(243,320))),
9:((AX,Q(15221,186480)),(HALF,Q(134,3885)),
   (THIRD,Q(108621,663040)),(FA,Q(78125,596736)),
   (FB,Q(78125,132608))),
11:((AX,Q(1894031,36771840)),(HALF,Q(64783,574560)),
    (THIRD,Q(15527457,54476800)),(FB,Q(21484375,205922304)),
    (SIX,Q(2673,29792)),(S7A,Q(74942413,210124800))),
13:((AX,Q(1232693496262979,42382499047004160)),
    (HALF,Q(154914431412869,3862988194388400)),
    (THIRD,Q(4035413081670039,22790040639815680)),
    (FA,Q(13445238508984375,237341994663223296)),
    (FB,Q(956994289818171875,6645575850570252288)),
    (S7B,Q(237100934228276867,3390599923760332800)),
    (S7C,Q(126941819652170803,678119984752066560)),
    (NINE,Q(4944993667603677,45580081279631360)),
    (TEN,Q(608335914359375,3244910083286256))),
}
def H(e):
 if any(z%2 for z in e):return Q(0)
 out=Q(1)
 for z in e:
  for j in range(z//2):out*=Q(2*j+1,2)
 for j in range(sum(e)//2):out/=j+2
 return out
def orbit(q):return sorted(set(permutations(tuple(abs(x) for x in q))))
def orbit_size(q):return len(orbit(q))*2**sum(x!=0 for x in q)
def orbit_average(q,e):
 if any(z%2 for z in e):return Q(0)
 perms=orbit(q)
 return sum((prod(p[i]**e[i] for i in range(4)) for p in perms),Q(0))/len(perms)
def monomials(d):
 for a in range(d+1):
  for b in range(d-a+1):
   for c in range(d-a-b+1):
    for e in range(d-a-b-c+1):yield(a,b,c,e)

checks=0
for degree,entries in C.items():
 assert sum(w for _,w in entries)==1 and all(w>0 for _,w in entries)
 checks+=len(entries)+1
 for q,w in entries:
  assert sum(v*v for v in q)==1;checks+=1
 for e in monomials(degree):
  actual=sum((w*orbit_average(q,e) for q,w in entries),Q(0))
  assert actual==H(e),(degree,e,actual,H(e))
  checks+=1
 print(f"degree={degree}, orbits={len(entries)}, "
       f"nodes={sum(orbit_size(q) for q,w in entries)}, "
       f"complete_monomials={comb(degree+4,4)}")
print("YM_S3_ROOT_FREE_RATIONAL_DESIGNS_PASS",checks)
