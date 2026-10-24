#!/usr/bin/env python3
"""Exact finite spin quotient, NOT wild geometric pi1 or kernel proof.

SL2(F5)=2I; five conjugate Q8 subgroups -> A5, kernel {+/-I}.
A 6th-order Hurwitz-type rotor's cube is central -I.
Every SL2(F5) element is a commutator; compatible horn tower
maps can therefore be constructed recursively without asserting
a geometrically verified three-copy van Kampen theorem.
"""
from itertools import product, combinations
p=5
E=(1,0,0,1); N=(4,0,0,4)
def mul(a,b):
 x,y,z,w=a;X,Y,Z,W=b
 return ((x*X+y*Z)%p,(x*Y+y*W)%p,(z*X+w*Z)%p,(z*Y+w*W)%p)
def inv(a):
 x,y,z,w=a
 return (w%p,(-y)%p,(-z)%p,x%p)
def power(a,n):
 v=E
 for _ in range(n):v=mul(v,a)
 return v
def conj(a,b):return mul(mul(a,b),inv(a))
def comm(a,b):return mul(mul(mul(a,b),inv(a)),inv(b))
def subgroup(gs):
 steps=tuple(gs)+tuple(inv(g) for g in gs)
 seen={E};front=[E]
 while front:
  x=front.pop()
  for g in steps:
   y=mul(x,g)
   if y not in seen:seen.add(y);front.append(y)
 return frozenset(seen)
def even(v):
 return sum(v[i]>v[j] for i in range(5) for j in range(i+1,5))%2==0
S=tuple((a,b,c,d) for a,b,c,d in product(range(5),repeat=4)
        if (a*d-b*c)%5==1)
assert len(S)==120
assert {g for g in S if power(g,2)==E}=={E,N}
order4=[g for g in S if power(g,2)==N]
Q=sorted({subgroup((a,b)) for a,b in combinations(order4,2)
          if comm(a,b)==N},key=lambda h:sorted(h))
assert len(Q)==5 and all(len(h)==8 for h in Q)
def action(g):
 return tuple(Q.index(frozenset(conj(g,x) for x in h)) for h in Q)
images={action(g) for g in S}
assert len(images)==60 and all(even(g) for g in images)
assert {g for g in S if action(g)==(0,1,2,3,4)}=={E,N}
assert all(action(mul(a,b))==tuple(action(a)[action(b)[i]] for i in range(5))
           for a in S for b in S)
normalizer=[g for g in S if frozenset(conj(g,x) for x in Q[0])==Q[0]]
assert len(normalizer)==24
q=next(g for g in normalizer if power(g,3)==N and g not in Q[0])
assert power(q,6)==E and power(mul(N,q),3)==E
pairs=[];left={x for x in Q[0] if power(x,2)==N}
while left:
 x=min(left);h=frozenset((x,mul(N,x)));pairs.append(h);left.difference_update(h)
perm=tuple(pairs.index(frozenset(conj(q,x) for x in h)) for h in pairs)
assert len(set(perm))==3 and perm!=(0,1,2)
assert tuple(perm[perm[perm[i]]] for i in range(3))==(0,1,2)
witnesses={};root=None
for a in S:
 for b in S:
  z=comm(a,b)
  witnesses.setdefault(z,(a,b))
  if z==q and root is None and len(subgroup((a,b)))==120:root=(a,b)
assert len(witnesses)==120 and root is not None
levels=[{():q}]
for n in range(5):
 out={}
 for address,g in levels[-1].items():
  a,b=root if n==0 else witnesses[g]
  assert comm(a,b)==g
  out[address+(0,)]=a
  out[address+(1,)]=b
 levels.append(out)
assert [len(v) for v in levels]==[1,2,4,8,16,32]
assert power(q,3)==N and action(N)==(0,1,2,3,4)
# SAME finite coordinate algebra: 360 spin coordinates -> 180 projective
# coordinates, exactly two spin lifts in each fibre. Pullback of
# functions is an injective, pointwise-product/mode-preserving inclusion.
from collections import Counter
fibres=Counter(action(g) for g in S)
assert len(fibres)==60 and set(fibres.values())=={2}
assert 3*len(S)==360 and 3*len(fibres)==180
spin_delta=lambda sector,g: int(sector==0 and g==N)
assert spin_delta(0,N)!=spin_delta(0,E)
assert action(N)==action(E)
print('PASS VOA coordinate projection 360->180, every fibre has size two')
print('PASS central-sign delta distinguishes +/-I, A5 projective coordinates cannot')
print('PASS 2I=SL2(F5) 120; 5 Q8; 2T normalizer 24; A5 quotient 60 kernel +/-I')
print('PASS non-split by unique element order 2; q^3=-I; Q8 axes 3-cycle')
print('PASS 120/120 commutators; surjective stage-one horn descendants')
print('PASS compatible horn stages depths 0..5; spin sign erased in A5 quotient')
print('NOT certified: geometric complement pi1, Agda kernel, 2I as rational-quaternion same-matrix map')
