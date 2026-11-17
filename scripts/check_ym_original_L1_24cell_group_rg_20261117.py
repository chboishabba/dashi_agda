#!/usr/bin/env python3
"""Exact original L=1 Wilson T2 Gibbs pushforward on 24-cell subgroup.

The rational S3 24-cell is closed under quaternion multiplication and
has degree-five Haar moments. Four original positive links produce
24**4 fine states. Coarse block is the actual noncommutative U0*U1.
Weight T2(beta*D)>0 is RATIONAL; original D has six commutators.
Verify positive coarse fibres, exact partition, pushforward and
conditional normalization. This is finite Taylor RG, NOT full exp Haar.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
from math import prod

V=[]
for axis in range(4):
 for sign in (-1,1):
  q=[Q(0)]*4;q[axis]=Q(sign);V.append(tuple(q))
for signs in product((-1,1),repeat=4):
 V.append(tuple(Q(s,2) for s in signs))
assert len(V)==len(set(V))==24
index={v:k for k,v in enumerate(V)}
def mul(a,b):
 p,q,r,s=a;t,u,v,w=b
 return(p*t-q*u-r*v-s*w,p*u+q*t+r*w-s*v,
        p*v-q*w+r*t+s*u,p*w+q*v-r*u+s*t)
def conjugate(a):return (a[0],-a[1],-a[2],-a[3])
M=[]
for q in V:
 row=[]
 for r in V:
  product_q=mul(q,r)
  assert product_q in index
  row.append(index[product_q])
 M.append(row)
identity=index[(Q(1),Q(0),Q(0),Q(0))]
assert all(M[identity][i]==M[i][identity]==i for i in range(24))
assert all(M[i][index[conjugate(V[i])]]==identity for i in range(24))
for i,j,k in product(range(24),repeat=3):
 assert M[M[i][j]][k]==M[i][M[j][k]]
assert all(set(M[i])==set(range(24)) for i in range(24))
assert all(set(M[j][i] for j in range(24))==set(range(24)) for i in range(24))
assert all(sum(x*x for x in q)==1 for q in V)
def poch(x,n):
 result=Q(1)
 for j in range(n):result*=x+j
 return result
def H(e):
 if any(k%2 for k in e):return Q(0)
 return prod(poch(Q(1,2),k//2) for k in e)/poch(Q(2),sum(e)//2)
moments=0
for a in range(6):
 for b in range(6-a):
  for c in range(6-a-b):
   for d in range(6-a-b-c):
    assert sum((q[0]**a*q[1]**b*q[2]**c*q[3]**d for q in V),Q(0))/24==H((a,b,c,d))
    moments+=1
def crossdef(i,j):
 a,b=V[i],V[j]
 return 2*sum((a[u]*b[v]-a[v]*b[u])**2 for u,v in ((1,2),(1,3),(2,3)))
D2=[[crossdef(i,j) for j in range(24)] for i in range(24)]
beta=Q(1,96);coarse=defaultdict(Q);Z=Q(0);N=Q(0);mom1=Q(0);mom2=Q(0)
for i,j,k,l in product(range(24),repeat=4):
 D=D2[i][j]+D2[i][k]+D2[i][l]+D2[j][k]+D2[j][l]+D2[k][l]
 S=beta*D
 w=1-S+S*S/2
 assert w>0
 blocked=M[i][j]
 coarse[blocked]+=w
 Z+=w;N+=w*V[blocked][0]
 mom1+=D;mom2+=D*D
fine=24**4
assert mom1/fine==Q(9,2) and mom2/fine==Q(187,8)
assert Z/fine==Q(140731,147456)
assert len(coarse)==24 and all(w>0 for w in coarse.values())
assert sum(coarse.values(),Q(0))==Z
assert sum((w/Z for w in coarse.values()),Q(0))==1
assert sum((w*V[a][0] for a,w in coarse.items()),Q(0))==N==0
assert all(sum(M[i][j]==a for i,j in product(range(24),repeat=2))==24 for a in range(24))
print("ORIGINAL_L1_24CELL_GROUP_RG_PASS",24**2+24**3+moments+fine)
print("fine states",fine,"blocked states",len(coarse))
print("exact partition",Z/fine,"blocked trace expectation",N/Z)
