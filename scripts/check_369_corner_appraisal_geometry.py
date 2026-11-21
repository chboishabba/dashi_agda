#!/usr/bin/env python3
"""H07 exact native Base369 corner x appraisal vs affine stable carrier.
Local SymPy only, and a native nearest-neighbour nonintertwining witness.
"""
from itertools import product
from collections import Counter
import sympy as s
T=(0,1,2)
S=(1,2)
def pivot(x):
 a,v,b=x
 t=pow(v[0],-1,3); aa=-a[0]*t%3; bb=-b[0]*t%3
 return ((aa,(a[1]+v[1]*aa)%3,(a[2]+v[2]*aa)%3),
         (t,v[1]*t%3,v[2]*t%3),
         (bb,(b[1]+v[1]*bb)%3,(b[2]+v[2]*bb)%3))
states=0
corners=Counter()
adjacency_counterexample=None
for signs in product(S,repeat=3):
 for a in product(T,repeat=3):
  for b in product(T,repeat=3):
   source=(a,signs,b)
   native=(tuple(-1 if q==2 else 1 for q in signs),a,b)
   assert (native[1],tuple(2 if q==-1 else 1 for q in native[0]),native[2])==source
   assert pivot(pivot(source))==source
   corners[native[0]]+=1
   states+=1
   for i in range(3):
    if a[i]<2:
     aa=list(a);aa[i]+=1;other=(tuple(aa),signs,b)
     first=pivot(source);second=pivot(other)
     changed=sum(x!=y for u,v in zip(first,second) for x,y in zip(u,v))
     if changed>1 and adjacency_counterexample is None:
      adjacency_counterexample=(source,other,first,second,changed)
assert states==5832
assert len(corners)==8 and set(corners.values())=={729}
assert 8*729==2**3*3**6==5832
assert adjacency_counterexample is not None
for p,q in product(corners,repeat=2):
 if p!=q: assert sum(abs(x-y) for x,y in zip(p,q))>=2
print('SymPy',s.__version__)
print('PASS',states,'two-sided native corner/appraisal addresses')
print('PASS 8 corner strata each with 729 appraisal states')
print('PASS',states,'selected affine pivot involutions')
print('COUNTEREXAMPLE pivot not native grid edge action:',adjacency_counterexample)
