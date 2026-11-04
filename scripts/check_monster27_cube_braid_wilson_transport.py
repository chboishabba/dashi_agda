#!/usr/bin/env python3
"""Exact braid-covariant Z27 discrete gauge/Wilson model on Cube27.
Pay 36 added nonlocal edges first: Eplus=E U M(E), 90 bonds.
This is a mathematical model, NOT an actual KK circle connection,
Monster VOA bulk action, or AdS3 duality.
"""
from itertools import product,combinations
import sympy as s
C=tuple(sorted(product((-1,0,1),repeat=3)))
res=lambda v:(v+1)%3-1
M=lambda p:(res(p[0]+p[1]),res(p[0]-p[1]),p[2])
canon=lambda a,b:tuple(sorted((a,b)))
dist=lambda a,b:sum(abs(x-y) for x,y in zip(a,b))
E={canon(a,b) for a in C for b in C if dist(a,b)==1}
F=E|{canon(M(a),M(b)) for a,b in E}
assert len(E)==54 and len(F)==90
assert {canon(M(a),M(b)) for a,b in F}==F
def push_edge(A):
 out={}
 for (p,q),value in A.items():
  P,Q=M(p),M(q)
  edge=canon(P,Q)
  out[edge]=(value if (P,Q)==edge else -value)%27
 assert len(out)==len(F)
 return out
push_vertex=lambda a:{M(p):a[p] for p in C}
d=lambda a:{(p,q):(a[q]-a[p])%27 for p,q in F}
A={edge:(7*i+3)%27 for i,edge in enumerate(sorted(F))}
alpha={p:(p[0]+2*p[1]+9*p[2])%27 for p in C}
assert push_edge(d(alpha))==d(push_vertex(alpha))
transformed={edge:(A[edge]+d(alpha)[edge])%27 for edge in F}
assert push_edge(transformed)=={
 edge:(push_edge(A)[edge]+d(push_vertex(alpha))[edge])%27 for edge in F}
four=A
for _ in range(4):four=push_edge(four)
assert four==A
idx={p:i for i,p in enumerate(C)}
P=s.zeros(27);L=s.zeros(27)
for p in C:P[idx[M(p)],idx[p]]=1
for p,q in F:
 i,j=idx[p],idx[q]
 L[i,i]+=1;L[j,j]+=1;L[i,j]-=1;L[j,i]-=1
assert P.T*P==s.eye(27) and L*P==P*L
assert s.trace(L)==180
def holonomy(A,path):
 return sum(A[(p,q)] if p<q else -A[(q,p)] for p,q in zip(path,path[1:]))%27
plaquettes=[]
for i,j in combinations(range(3),2):
 h=next(t for t in range(3) if t not in (i,j))
 for vi,vj,vh in product((-1,0),(-1,0),(-1,0,1)):
  v=[0,0,0];v[i]=vi;v[j]=vj;v[h]=vh
  p=tuple(v);v[i]+=1;pi=tuple(v);v[i]-=1;v[j]+=1;pj=tuple(v);v[i]+=1;pij=tuple(v)
  plaquettes.append((p,pi,pij,pj,p))
assert len(plaquettes)==36
for loop in plaquettes:
 mapped=tuple(map(M,loop))
 assert all(canon(p,q) in F for p,q in zip(mapped,mapped[1:]))
 assert holonomy(A,loop)==holonomy(push_edge(A),mapped)
 assert holonomy(A,loop)==holonomy(transformed,loop)
print('PASS native Cube27 with 36 additional M-orbit bonds gives 90-edge graph')
print('PASS M graph/Laplacian symmetry and order-four cochain action')
print('PASS lattice gauge differential commutes with M transport')
print('PASS all 36 native plaquette Wilson loops covariant and gauge invariant')
print('OPEN real source-backed VOA field operators, continuum KK metric and AdS3 dual')
