#!/usr/bin/env python3
"""Constructive Sah/Griess SL3(3) complement on the ORIGINAL M81.

External ORIGINAL roots: C.-H. Sah, J Algebra 29 (1974) 255-302;
R. L. Griess Jr, Pacific J Math 63 (1976) 405-409 (H²=0);
Griess Jr, J Algebra 131 (1990) 281-293 (this particular source g).
DASHI: later explicit finite search and algebraic evidence, NOT the
original cohomological theorem, Lean/Agda proof, or physical model.

This is a fully runnable independent finite solver with NumPy/SymPy.
"""
from collections import Counter,deque
from itertools import product
import numpy as np
from sympy.combinatorics import Permutation,PermutationGroup

V=tuple(product(range(3),repeat=3))
vindex={x:i for i,x in enumerate(V)}
S=tuple((i,j) for i in range(3) for j in range(3) if i!=j)
def sh(x,i,j):
 y=list(x);y[i]=(y[i]+y[j])%3;return tuple(y)
def g(x,y):
 a,b,c=x;p,q,r=y;return (-a*b*r-c*p*q+b*c*p+a*q*r)%3
def phase(x,i,j):
 a,b,c=x
 return {(0,1):c*(1-b*b),(0,2):0,(1,0):c*(1-a*a),
         (1,2):a*(c*c-1),(2,0):0,(2,1):a*(b*b-1)}[i,j]%3

mapsG=[];features=[]
for j,(i,k) in enumerate(S):
 G=np.array([vindex[sh(x,i,k)] for x in V],dtype=np.uint8)
 H=np.zeros((19,27),dtype=np.uint8)
 H[0]=[phase(x,i,k) for x in V]
 for r in range(3):H[1+3*j+r]=[V[G[t]][r] for t in range(27)]
 mapsG.append(G);features.append(H)
 for x,y in product(V,repeat=2):
  z=tuple((a+b)%3 for a,b in zip(x,y))
  assert (phase(z,i,k)-phase(x,i,k)-phase(y,i,k)
          -g(sh(x,i,k),sh(y,i,k))+g(x,y))%3==0

ident=np.arange(27,dtype=np.uint8)
maps=[ident];affine=[np.zeros((19,27),dtype=np.uint8)]
lookup={ident.tobytes():0};queue=deque([0])
pivots={};eqs=0;inconsistent=0;edges=0
def add_equation(r):
 global eqs,inconsistent
 v=[int(z)%3 for z in r];eqs+=1
 for k in sorted(pivots):
  if v[k]:
   a=v[k];p=pivots[k]
   v[0]=(v[0]-a*p[0])%3
   for t in range(k,19):v[t]=(v[t]-a*p[t])%3
 for k in range(1,19):
  if v[k]:
   a=1 if v[k]==1 else 2
   v[0]=(v[0]*a)%3
   for t in range(k,19):v[t]=(v[t]*a)%3
   pivots[k]=v
   return
 if v[0]:inconsistent+=1

while queue:
 n=queue.popleft();G=maps[n];H=affine[n]
 for j in range(6):
  target=mapsG[j][G];key=target.tobytes()
  proposed=((H.astype(np.int16)+features[j][:,G].astype(np.int16))%3).astype(np.uint8)
  if key not in lookup:
   lookup[key]=len(maps);maps.append(target);affine.append(proposed)
   queue.append(len(maps)-1)
  else:
   diff=(proposed.astype(np.int16)-affine[lookup[key]].astype(np.int16))%3
   for column in diff.T:add_equation(column)
  edges+=1
assert (len(maps),edges,eqs,len(pivots),inconsistent)==(5616,33696,758187,15,0)
sol=[0]*19
for k in sorted(pivots,reverse=True):
 row=pivots[k]
 sol[k]=(-row[0]-sum(row[t]*sol[t] for t in range(k+1,19)))%3
L=tuple(tuple(sol[1+3*j:1+3*j+3]) for j in range(6))
assert L==((0,0,0),(0,2,0),(0,0,1),(2,0,0),(0,1,0),(0,0,0))
def eval_affine(H):
 return (H[0].astype(np.int16)+np.asarray(sol[1:],dtype=np.int16) @ H[1:].astype(np.int16))%3
values={key:eval_affine(affine[n]) for key,n in lookup.items()}
for G,H in zip(maps,affine):
 h=eval_affine(H)
 for j in range(6):
  assert np.array_equal((h+eval_affine(features[j])[G])%3,values[mapsG[j][G].tobytes()])

# All solutions of the 18-variable system are exactly the 27
# conjugates by the ORIGINAL central-character kernel F3^3.
solutions=set()
for mu in V:
 trial=sol.copy()
 for j,(i,k) in enumerate(S):trial[1+3*j+k]=(trial[1+3*j+k]+mu[i])%3
 assert all((p[0]+sum(p[t]*trial[t] for t in range(1,19)))%3==0 for p in pivots.values())
 solutions.add(tuple(trial[1:]))
assert len(solutions)==3**(18-len(pivots))==27

M=tuple(product(V,range(3)));mindex={a:i for i,a in enumerate(M)}
lifts=[]
for j,(i,k) in enumerate(S):
 p=Permutation([mindex[(sh(x,i,k),(a+phase(x,i,k)+
             sum(L[j][r]*sh(x,i,k)[r] for r in range(3)))%3)]
             for x,a in M])
 assert p.order()==3
 lifts.append(p)
G=PermutationGroup(lifts)
assert G.order()==5616

# Independent exact character audit from ALL ACTUAL permutation group
# elements, not merely the linear-system symbolic representative words.
chi=Counter();chi_points=Counter()
for perm in G.generate_schreier_sims():
 fixed=Counter();nfixed=0
 for x in V:
  x2,a2=M[perm(mindex[(x,0)])]
  if x2==x:
   nfixed+=1;fixed[a2]+=1
 assert fixed[1]==fixed[2]
 chi[fixed[0]-fixed[2]-1]+=1
 chi_points[nfixed-1]+=1
assert chi=={-1:1664,0:3132,2:819,26:1}
assert sum(v for v in chi.values())==5616
assert sum(k*v for k,v in chi.items())==0
assert sum(k*k*v for k,v in chi.items())==5616
assert sum(k*k*v for k,v in chi_points.items())==3*5616
for gm,H in zip(maps,affine):
 fixed=Counter(int(eval_affine(H)[k]) for k in range(27) if gm[k]==k)
 assert fixed[1]==fixed[2]
assert all(sum((phase(x,*S[j])+sum(L[j][r]*sh(x,*S[j])[r]
            for r in range(3)))%3==q for x in V if sh(x,*S[j])==x)==3
           for j in range(6) for q in range(3))
print('PASS coherent original M81 section: grade SL3 size5616, 33696 edges, GF3 rank15')
print('PASS all 758187 equations, unique 27 kernel-conjugate sections')
print('PASS actual 81-element generator permutation group of order5616')
print('PASS 5616 group characters: actual Albert J0 norm1, irreducible')
print('PASS grade26 permutation character norm3, not full-group equivalent')
print('OPEN Lean/Agda kernel, physical adjacency, Monster VOA or full F4 classification')
