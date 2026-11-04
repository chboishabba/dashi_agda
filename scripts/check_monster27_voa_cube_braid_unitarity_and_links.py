#!/usr/bin/env python3
"""Exact Monster Vnatural_2 C27 eigencharge vs Cube27 braid/operator tests.
Premises: T_27/T_9B/T_3B coefficients 3/0/54 and rational Monster
representation. Abstract block intertwiners are NOT literal VOA modes.
"""
from itertools import product
from math import gcd
from collections import Counter
C=tuple(sorted(product((-1,0,1),repeat=3)))
k=lambda p:(p[0]+3*p[1]+9*p[2])%27
order=lambda a:27//gcd(a,27)
ranks={1:7298,3:7295,9:7296,27:7290}
rank=lambda p:ranks[order(k(p))]
m=lambda a:((a+1)%3)-1
M=lambda p:(m(p[0]+p[1]),m(p[0]-p[1]),p[2])
assert len(C)==27 and sum(map(rank,C))==196884
assert Counter(map(rank,C))=={7298:1,7295:2,7296:6,7290:18}
unseen=set(C);cycles=[]
while unseen:
 p=min(unseen);o=[];q=p
 while q not in o:o.append(q);unseen.remove(q);q=M(q)
 assert q==p;cycles.append(o)
assert Counter(map(len,cycles))=={4:6,1:3}
mixed=[o for o in cycles if len(set(map(rank,o)))>1]
assert len(mixed)==3
assert all(sorted(map(rank,o))==[7290,7290,7296,7296] for o in mixed)
padding=sum(sum(max(map(rank,o))-rank(p) for p in o) for o in cycles)
truncate=sum(sum(rank(p)-min(map(rank,o)) for p in o) for o in cycles)
assert padding==truncate==36
# No rank-preserving permutation of all actual VOA charge eigenspaces.
assert order(k((0,1,0)))==9 and order(k(M((0,1,0))))==27
# Hence M cannot normalize g as an automorphism of cyclic order-27 group.
assert all(order((a*k((0,1,0)))%27)==9 for a in range(27) if gcd(a,27)==1)
E={tuple(sorted((p,q))) for p in C for q in C
   if sum(abs(x-y) for x,y in zip(p,q))==1}
assert len(E)==54
byaxis=Counter()
for p,q in E:
 axis=next(i for i in range(3) if p[i]!=q[i])
 d=(k(q)-k(p))%27
 assert d in (3**axis,(-3**axis)%27)
 byaxis[axis]+=1
 assert min(rank(p),rank(q))>0
 # Matter transition E_p->E_q of charge d accompanied by link
 # lowering of charge -d preserves total global C27 charge.
 for a in range(27):
  assert (k(q)+a-d)%27 == (k(p)+a)%27
assert byaxis=={0:18,1:18,2:18}
print("PASS full Vnatural2 rank census and mixed braid cycles")
print("PASS whole-fibre M unitary impossible; minimum 36-dimensional padding/truncation")
print("PASS 9th-order->27th-order mismatch prevents C27 power-map normalization")
print("PASS all 54 abstract edge operators have nonzero rank and link compensation")
print("OPEN actual nonzero selected VOA mode, charged gauge-field dynamics, gravity")
