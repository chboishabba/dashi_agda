#!/usr/bin/env python3
"""Exact native 3x3x3 cube / genuine Monster-C27 charge audit.

Source premises: FLM, ATLAS 27A/B power maps, q1 characters 3/0/54,
and Griess algebra unit e=omega/2 with u_(1)e=u.
The latter is an external VOA theorem, NOT computed from Monster matrices.
"""
from itertools import product, permutations
from collections import Counter
from math import gcd
sites=tuple(product((-1,0,1),repeat=3))
charge=lambda p:sum(3**i*p[i] for i in range(3))%27
conductor=lambda p:27//gcd(charge(p),27)
ranks={1:7298,3:7295,9:7296,27:7290}
rank=lambda p:ranks[conductor(p)]
assert Counter(rank(p) for p in sites)=={7298:1,7295:2,7296:6,7290:18}
edges=set()
for p in sites:
 for axis in range(3):
  q=list(p);q[axis]+=1
  if q[axis]<=1:edges.add((p,tuple(q),axis))
assert len(edges)==54
assert all((charge(q)-charge(p))%27==3**a for p,q,a in edges)
spokes=[(p,q,a) for p,q,a in edges if (0,0,0) in (p,q)]
assert len(spokes)==6
assert sorted(rank(q if p==(0,0,0) else p) for p,q,a in spokes)==[
 7290,7290,7295,7295,7296,7296]
# These 6 geometry edges have a source-supported nonzero grade-two
# transition from e to a charged state: u_(1)e=u. For the other
# 48 native edges no explicit numerical Vnatural first-mode product
# has yet been sourced. Do not mark them as paid.
assert len(edges)-len(spokes)==48

# Exact intersection of cube graph automorphisms (signed coordinate
# permutations) with C27 power automorphisms of the charge chart.
intersection=[]
for perm in permutations(range(3)):
 for signs in product((-1,1),repeat=3):
  f=lambda p:tuple(signs[i]*p[perm[i]] for i in range(3))
  for unit in range(27):
   if gcd(unit,27)==1 and all(charge(f(p))==unit*charge(p)%27 for p in sites):
    intersection.append((perm,signs,unit))
assert intersection==[
 ((0,1,2),(-1,-1,-1),26),((0,1,2),(1,1,1),1)]
# Weighted local gauge transformations alpha_p -> beta_p=k_p*alpha_p
# do not act faithfully; a given beta has gcd(27,k_p) preimages.
kernel=1
for p in sites:kernel*=gcd(27,charge(p))
assert kernel==3**13==1594323
modular=lambda p:(((p[0]+p[1]+1)%3)-1,
                  ((p[0]-p[1]+1)%3)-1,p[2])
assert sum(rank(modular(p))!=rank(p) for p in sites)==12
print("PASS 27 weighted source charge addresses and 54 cube edges")
print("PASS exactly 6 centre incident edges have the source VOA Griess-unit mode witness")
print("OPEN 48 remaining noncentral first-mode amplitudes")
print("PASS cube graph automorphism x C27 charge-power symmetry intersection C2={+I,-I}")
print("PASS endpoint-weighted gauge site-parameter kernel size 3^13")
print("PASS 12 sites have whole-fibre rank mismatch under selected mod3 braid")
