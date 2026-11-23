#!/usr/bin/env python3
"""Exhaustive native Base369 grid/consumer vs pivot02 transport.
Independent finite SymPy test; no CI and no Agda kernel acceptance.
"""
from itertools import product
from collections import Counter
import sympy as s
T=range(3);SIG=(1,2)
def pivot(x):
 a,v,b=x;t=pow(v[0],-1,3);aa=-a[0]*t%3;bb=-b[0]*t%3
 return ((aa,(a[1]+v[1]*aa)%3,(a[2]+v[2]*aa)%3),
         (t,v[1]*t%3,v[2]*t%3),
         (bb,(b[1]+v[1]*bb)%3,(b[2]+v[2]*bb)%3))
def neighbors(x):
 for k,name in ((0,"appraisalA"),(2,"appraisalB")):
  for i in range(3):
   for step in (-1,1):
    if 0<=x[k][i]+step<=2:
     z=[list(t) for t in x];z[k][i]+=step
     yield tuple(map(tuple,z)),(name,i)
def native_adjacent(x,y):
 return x[1]==y[1] and sum(abs(u-v) for t,w in ((x[0],y[0]),(x[2],y[2])) for u,v in zip(t,w))==1
def corner(x):return x[1]
def native_consumer(x):return x[1],x[0],x[2]
def support(x):return sum(t==0 for row in (x[0],x[2]) for t in row)
count=Counter();axes=Counter();consumers=Counter();negative=None
for v in product(SIG,repeat=3):
 for a in product(T,repeat=3):
  for b in product(T,repeat=3):
   x=(a,v,b);p=pivot(x)
   assert pivot(p)==x
   count["states"]+=1
   assert native_consumer(pivot(p))==native_consumer(x)
   assert native_consumer(pivot(p))[0]==corner(x)
   for label,func in (("corner",corner),("appraisalA",lambda t:t[0]),
                      ("appraisalB",lambda t:t[2]),("zero-support",support)):
    consumers[(label,func(p)==func(x))]+=1
   for y,axis in neighbors(x):
    if x<y:
     valid=native_adjacent(p,pivot(y))
     axes[(*axis,valid)]+=1
     count["edge-preserved" if valid else "edge-not-preserved"]+=1
     if not valid and negative is None:negative=(x,y,p,pivot(y))
assert count["states"]==5832
assert count["edge-preserved"]==10368 and count["edge-not-preserved"]==12960
assert negative is not None
print("SymPy",s.__version__)
print("PASS native vertices",count["states"],"native edges",count["edge-preserved"]+count["edge-not-preserved"])
print("PRESERVED",count["edge-preserved"],"BROKEN",count["edge-not-preserved"])
print("BY_AXIS",sorted(axes.items()))
print("CONSUMERS",sorted(consumers.items()))
print("NEGATIVE_CONTROL",negative)
print("PASS all 5832 pulled-back native consumers by exact pivot inverse")
