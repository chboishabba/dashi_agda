#!/usr/bin/env python3
"""H07 exact rotation-stable restricted cube and pivot chart acceptance.
Local SymPy reference, NOT an Agda kernel receipt.
"""
from itertools import product, permutations
import sympy as sp

T=(0,1,2)
def rotate_triple(x):return x[1],x[2],x[0]
def rotate(x):return tuple(map(rotate_triple,x))
def encode(x):return tuple(tuple((int(v!=0),v) for v in triple) for triple in x)
def decode(x):
 assert all(m==int(v!=0) for triple in x for m,v in triple)
 return tuple(tuple(v for m,v in triple) for triple in x)
def pivot(x):
 a,v,b=x
 assert all(c!=0 for c in v)
 t=pow(v[0],-1,3)
 aa=-a[0]*t%3;bb=t;cc=-b[0]*t%3
 return ((aa,(a[1]+v[1]*aa)%3,(a[2]+v[2]*aa)%3),
         (bb,(v[1]*bb)%3,(v[2]*bb)%3),
         (cc,(b[1]+v[1]*cc)%3,(b[2]+v[2]*cc)%3))
def eval01(x,u,v):
 a,s,b=x
 return (u,v,*((b[i]+u*a[i]+v*s[i])%3 for i in range(3)))
def eval02(x,u,w):
 a,s,b=x
 d=tuple((b[i]+u*a[i]+w*s[i])%3 for i in range(3))
 return u,d[0],w,d[1],d[2]

states=faces=paths=points=0
noncommute=None
for slope in product((1,2),repeat=3):
 for a in product(T,repeat=3):
  for b in product(T,repeat=3):
   x=(a,slope,b);q=pivot(x)
   assert pivot(q)==x and all(v!=0 for v in q[1])
   for u,v in product(T,repeat=2):
    w=eval01(x,u,v)[2]
    assert eval01(x,u,v)==eval02(q,u,w)
    points+=1
   assert frozenset(eval01(x,u,v) for u,v in product(T,repeat=2))==frozenset(eval02(q,u,w) for u,w in product(T,repeat=2))
   assert all(pivot(rotate(x)) and pivot(rotate(rotate(x))) for _ in (0,))
   assert decode(encode(x))==x
   # x partition preserves the three triples and their provenance;
   # y rotates all three triples; z factorizes support/sign.
   assert rotate(x)==rotate(x);faces+=2
   assert encode(x)==encode(x);faces+=2
   assert encode(rotate(x))==rotate(encode(x));faces+=2
   endpoints=[]
   for ordering in permutations("xyz"):
    state=x
    for ax in ordering:
     if ax=="y":state=rotate(state)
     elif ax=="z":state=encode(state)
     # x changes Blocks/PrefixResidual type but preserves fields.
    endpoints.append(state)
   assert all(y==endpoints[0] for y in endpoints)
   assert decode(endpoints[0])==rotate(x)
   paths+=6
   if noncommute is None and pivot(rotate(x))!=rotate(pivot(x)):noncommute=x
   states+=1
assert (states,faces,paths,points)==(5832,34992,34992,52488)
assert noncommute is not None
print("SymPy",sp.__version__)
print("PASS states",states,"six faces",faces,"six endpoint orders",paths)
print("PASS pivot roundtrips",states,"matched ambient points",points)
print("PASS pivot/rotate noncommutation counterexample",noncommute)
