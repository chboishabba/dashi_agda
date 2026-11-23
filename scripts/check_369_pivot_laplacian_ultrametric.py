#!/usr/bin/env python3
"""H07 native edge Laplacian and ordered ternary-prefix ultrametric screen.
Execute locally using Python and SymPy. Neither CI nor Agda required.
"""
from itertools import product
import sympy as sp
T=range(3); S=(1,2)
def pivot(x):
 a,v,b=x;t=pow(v[0],-1,3);aa=-a[0]*t%3;bb=-b[0]*t%3
 return ((aa,(a[1]+v[1]*aa)%3,(a[2]+v[2]*aa)%3),
         (t,v[1]*t%3,v[2]*t%3),
         (bb,(b[1]+v[1]*bb)%3,(b[2]+v[2]*bb)%3))
def neighbors(x):
 for k in (0,2):
  for i in range(3):
   for d in (-1,1):
    if 0<=x[k][i]+d<=2:
     z=[list(t) for t in x];z[k][i]+=d
     yield tuple(map(tuple,z))
def native_adj(x,y):
 return x[1]==y[1] and sum(abs(a-b) for z,w in ((x[0],y[0]),(x[2],y[2])) for a,b in zip(z,w))==1
states=[(a,v,b) for v in product(S,repeat=3) for a in product(T,repeat=3) for b in product(T,repeat=3)]
lookup={x:i for i,x in enumerate(states)}
P=[lookup[pivot(x)] for x in states]
assert len(states)==5832 and len(set(P))==5832
assert all(P[P[i]]==i for i in range(5832))
edges=[(i,lookup[y]) for i,x in enumerate(states) for y in neighbors(x) if i<lookup[y]]
assert len(edges)==23328
transport={(min(P[i],P[j]),max(P[i],P[j])) for i,j in edges}
assert len(transport)==23328
native_after=sum(native_adj(states[P[i]],states[P[j]]) for i,j in edges)
assert native_after==10368
def L(v):
 o=[0]*5832
 for i,j in edges:
  d=v[i]-v[j];o[i]+=d;o[j]-=d
 return o
def energy(v):return sum((v[i]-v[j])**2 for i,j in edges)
def carry(v):
 o=[0]*5832
 for i,j in enumerate(P):o[j]=v[i]
 return o
def pull(v):return [v[P[i]] for i in range(5832)]
fixtures=[[(i*31+7)%17-8 for i in range(5832)],
          [sum(x[0])+2*sum(x[2]) for x in states],
          [int(x[1][0]==1) for x in states]]
failures=[]
for idx,f in enumerate(fixtures):
 g=carry(f); transported=carry(L(pull(g)))
 assert transported==carry(L(f)) and energy(pull(g))==energy(f)
 naive=L(g)
 if naive!=transported:failures.append((idx,sum(a!=b for a,b in zip(naive,transported)),energy(g),energy(f)))
assert failures
def prefix_depth(x,y):
 a=x[1]+x[0]+x[2];b=y[1]+y[0]+y[2]
 return next((i for i,(u,v) in enumerate(zip(a,b)) if u!=v),9)
checked=0
for i in range(0,5832,13):
 for j in range(0,5832,17):
  assert prefix_depth(states[i],states[j])==prefix_depth(states[P[i]],states[P[j]])
  checked+=1
assert checked==154456
print('SymPy',sp.__version__)
print('PASS',len(states),'states;',len(edges),'native edges; transported edges',len(transport))
print('Native adjacency retained',native_after,'lost',len(edges)-native_after)
print('PASS',len(fixtures),'integer 5832-vector Laplacian conjugacies and exact transported energies')
print('PASS',checked,'selected ordered nine-digit prefix comparisons')
print('NEGATIVE naive untransported Laplacian',failures)
