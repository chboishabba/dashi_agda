#!/usr/bin/env python3
"""Exhaustive exact prefix-partition certificate, all 5832 finite states."""
from itertools import product
from collections import defaultdict
import sympy as sp

T=range(3); S=(1,2)
def pivot(state):
 v=state[:3];a=state[3:6];b=state[6:];t=pow(v[0],-1,3)
 aa=-a[0]*t%3;bb=-b[0]*t%3
 return (t,v[1]*t%3,v[2]*t%3,aa,(a[1]+v[1]*aa)%3,(a[2]+v[2]*aa)%3,bb,(b[1]+v[1]*bb)%3,(b[2]+v[2]*bb)%3)
states=[v+a+b for v in product(S,repeat=3) for a in product(T,repeat=3) for b in product(T,repeat=3)]
images=[pivot(x) for x in states]
assert len(states)==5832 and len(set(images))==5832
assert all(pivot(y)==x for x,y in zip(states,images))
partitions=[]
for depth in range(10):
 old=defaultdict(set);new=defaultdict(set)
 for i,(x,y) in enumerate(zip(states,images)):
  old[x[:depth]].add(i);new[y[:depth]].add(i)
 old_classes=set(map(frozenset,old.values()))
 new_classes=set(map(frozenset,new.values()))
 assert old_classes==new_classes,(depth,len(old),len(new))
 partitions.append((depth,len(old_classes),sorted(set(map(len,old_classes)))))
print('SymPy',sp.__version__,'all-pairs prefix certificate PASS')
print('All 10 prefix partitions identical:',partitions)
print('Unordered distinct pairs covered:',len(states)*(len(states)-1)//2)
# Alternate order puts A1 ahead of A0, violating a true dependency.
order=(0,4,1,2,3,5,6,7,8)
def prefix(x):return tuple(x[i] for i in order)
buckets={}
for x,y in zip(states,images):
 k=prefix(x)[:2];prev=buckets.get(k)
 if prev is not None and prefix(prev[1])[:2]!=prefix(y)[:2]:
  print('ALTERNATE-ORDER COUNTEREXAMPLE',order,prev[0],x,prev[1],y)
  break
 buckets[k]=(x,y)
else:raise AssertionError('missing alternative-order negative control')
for k in range(10):
 f={}
 for x,y in zip(states,images):
  inp=x[:k];out=y[:k]
  if inp in f:assert f[inp]==out
  else:f[inp]=out
 assert len(f)==len(set(f.values()))
print('All 10 induced prefix maps well-defined and bijective: PASS')
