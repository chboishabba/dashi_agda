#!/usr/bin/env python3
"""Q8 finite 4D site-plane reflection/blocking BIDI, not Agda proof."""
from itertools import product
from random import Random
Q=tuple((s,a) for s in (1,-1) for a in range(4))
cross={(1,2):(1,3),(2,3):(1,1),(3,1):(1,2),
       (2,1):(-1,3),(3,2):(-1,1),(1,3):(-1,2)}
def mul(x,y):
 s,a=x;t,b=y
 if a==0:return (s*t,b)
 if b==0:return (s*t,a)
 if a==b:return (-s*t,0)
 u,c=cross[a,b];return (s*t*u,c)
def inv(x):
 s,a=x
 return (s,0) if a==0 else (-s,a)
def step(site,axis,d,L):
 z=list(site);z[axis]=(z[axis]+d)%L;return tuple(z)
def theta(site,L):return ((-site[0])%L,*site[1:])
def block(U,site,axis):
 x=tuple(2*t for t in site)
 return mul(U[(x,axis)],U[(step(x,axis,1,4),axis)])
def reflected(U):
 R={}
 for site in product(range(4),repeat=4):
  for axis in range(4):
   t=theta(site,4)
   R[(site,axis)]=inv(U[(step(t,0,-1,4),0)]) if axis==0 else U[(t,axis)]
 return R
rng=Random(20261106)
coarse=list(product(product(range(2),repeat=4),range(4)))
assert len(coarse)==64
bad=0
for _ in range(32):
 U={(site,a):rng.choice(Q) for site in product(range(4),repeat=4) for a in range(4)}
 R=reflected(U)
 for site,axis in coarse:
  t=theta(site,2)
  rhs=inv(block(U,step(t,0,-1,2),0)) if axis==0 else block(U,t,axis)
  lhs=block(R,site,axis)
  assert lhs==rhs
  if axis==0 and lhs!=block(U,t,axis):bad+=1
assert bad>0
print("PASS 2048 actual side-four to side-two Q8 reflected ordered bonds")
print("PASS deliberate non-reversing time reflection negative controls:",bad)
