#!/usr/bin/env python3
"""Exact 27-charge Frobenius countermodel and Griess non-promotion audit.

EXTERNAL: FLM actual Vnatural2 weight2 rational Monster action, published
27A/B, 9B, 3B twining q coefficients and Griess unit/invariant pairing.
THIS FILE'S sparse products are *countermodels*, NOT the Vnatural algebra.
They show common source-compatible axioms don't force specific cube-edge
mode-one amplitudes. Full 196884 dimension; normalization <e,e>=c/8=3 for c=24. Sparse arithmetic.
"""
from collections import Counter
from itertools import product
from fractions import Fraction
from math import gcd
N=27
R={1:7298,3:7295,9:7296,27:7290}
rank=lambda k:R[N//gcd(k,N)]
assert sum(rank(k) for k in range(N))==196884
assert all(rank(k)==rank(-k) for k in range(N))
e=(0,0)
def basis(k,i=0):
 k%=N
 assert 0<=i<rank(k)
 return (k,i)
def pairing(a,b):
 return 3 if a==e and b==e else int((a[0]+b[0])%N==0 and a[1]==b[1])
def dual(a):return ((-a[0])%N,a[1])
# C(1,3,-4) is an invariant totally symmetric trilinear form.
a,b,c=basis(1),basis(3),basis(23)
triangle={a,b,c}
assert sum(k for k,i in triangle)%N==0
def multiply(u,v,t=Fraction(0)):
 if u==e:return {v:Fraction(1)}
 if v==e:return {u:Fraction(1)}
 out={}
 if pairing(u,v):out[e]=Fraction(pairing(u,v),3)
 if t and u!=v and u in triangle and v in triangle:
  w=next(x for x in triangle if x!=u and x!=v)
  dw=dual(w)
  out[dw]=out.get(dw,Fraction(0))+t
 return out
def contract(o,w):
 return sum((coef*pairing(x,w) for x,coef in o.items()),Fraction(0))
samples=[e]+[basis(k) for k in range(1,N)]+[basis(0,1)]
samples.extend(basis(k,1) for k in (1,3,4,23,26))
for t in (Fraction(0),Fraction(1),Fraction(7,3)):
 for u in samples:
  assert multiply(e,u,t)==multiply(u,e,t)=={u:1}
  for v in samples:
   assert multiply(u,v,t)==multiply(v,u,t)
   assert all(w[0]==(u[0]+v[0])%N for w in multiply(u,v,t))
   for w in samples:
    assert contract(multiply(u,v,t),w)==contract(multiply(v,w,t),u)
 for k in range(N):
  v=basis(k,1 if k==0 else 0)
  assert pairing(v,dual(v))==1
  assert contract(multiply(v,dual(v),t),e)==1

cube=set(product((-1,0,1),repeat=3))
address=lambda p:(p[0]+3*p[1]+9*p[2])%27
edges=set()
for p in cube:
 for axis in range(3):
  q=list(p);q[axis]+=1
  if q[axis]<=1:edges.add((p,tuple(q),axis))
assert len(cube)==27 and len(edges)==54
assert all((address(q)-address(p))%N==3**i for p,q,i in edges)
assert all((address(p)+address(q))%N!=0 for p,q,i in edges)
spokes=[(p,q,i) for p,q,i in edges if (0,0,0) in (p,q)]
assert len(spokes)==6 and len(edges)-len(spokes)==48
inverse_pairs={frozenset((p,tuple(-x for x in p))) for p in cube
               if p!=(0,0,0)}
assert len(inverse_pairs)==13
assert all(sum(abs(p[i]-q[i]) for i in range(3))%2==0
           for pair in inverse_pairs for p,q in [tuple(pair)])
# An original cube nearest-neighbour pair with charges 3 -> 4:
p=(0,1,0);q=(1,1,0)
assert (p,q,0) in edges and (address(p),address(q))==(3,4)
assert multiply(basis(1),basis(3),0)=={}
assert multiply(basis(1),basis(3),1)=={basis(4):1}
assert multiply(basis(1),basis(3),Fraction(7,3))=={basis(4):Fraction(7,3)}
print('PASS full Monster V2 charge-rank census and opposite-charge dual pairing')
print('PASS two non-Monster algebras with identical unital Frobenius and C27 covariance')
print('PASS 13 inverse-charge pairs and 6 neutral-site spokes; 48 other edges not fixed')
print('PASS noncentral edge first-mode amplitude can be zero or nonzero in countermodels')
print('NO CLAIM about actual Vnatural Griess multiplication for these 48 edges')
