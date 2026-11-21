#!/usr/bin/env python3
"""H07: exhaustive actual pivot02 conjugated cube (local SymPy reference).
Run python scripts/check_369_pivot02_recharted_cube.py; no CI or Agda.
"""
from itertools import product, permutations
import sympy as s
T=range(3)
def rot(t): return (t[1],t[2],t[0])
def R(x): return tuple(map(rot,x))
def Z(x): return tuple(tuple((int(v!=0),v) for v in row) for row in x)
def D(x):
 assert all(m==int(v!=0) for row in x for m,v in row)
 return tuple(tuple(v for m,v in row) for row in x)
def P(x):
 A,V,B=x
 assert all(V)
 t=pow(V[0],-1,3)
 aa=(-A[0]*t)%3; bb=(-B[0]*t)%3
 return ((aa,(A[1]+V[1]*aa)%3,(A[2]+V[2]*aa)%3),
         (t,(V[1]*t)%3,(V[2]*t)%3),
         (bb,(B[1]+V[1]*bb)%3,(B[2]+V[2]*bb)%3))
def E01(x,u,v):
 A,V,B=x
 return (u,v,*((B[i]+u*A[i]+v*V[i])%3 for i in range(3)))
def E02(x,u,w):
 A,V,B=x
 d=tuple((B[i]+u*A[i]+w*V[i])%3 for i in range(3))
 return (u,d[0],w,d[1],d[2])
def chart(st):
 x,y,z,w=st; a=P(D(w) if z else w)
 return (x,y,z,Z(a) if z else a)
def unchart(st):
 x,y,z,w=st; a=P(D(w) if z else w)
 return (x,y,z,Z(a) if z else a)
def source_step(st,axis):
 x,y,z,w=st
 if axis=='x':
  assert x==0
  return (1,y,z,w)
 if axis=='y':
  assert y==0
  return (x,1,z,R(w))
 assert axis=='z' and z==0
 return (x,y,1,Z(w))
def step(st,axis): return chart(source_step(unchart(st),axis))
count=face=paths=points=0; counter=None
for v in product((1,2),repeat=3):
 for a in product(T,repeat=3):
  for b in product(T,repeat=3):
   p=(a,v,b); q=P(p)
   assert P(q)==p and all(q[1])
   for u,t in product(T,repeat=2):
    assert E01(p,u,t)==E02(q,u,E01(p,u,t)[2])
    points+=1
   at={}
   for x,y,z in product((0,1),repeat=3):
    data=R(p) if y else p
    if z:data=Z(data)
    st=(x,y,z,data)
    at[(x,y,z)]=chart(st)
    assert unchart(chart(st))==st
   for key,i,j in (((0,0,0),'x','y'),((0,0,0),'x','z'),((0,0,0),'y','z'),
                   ((0,0,1),'x','y'),((0,1,0),'x','z'),((1,0,0),'y','z')):
    left=step(step(at[key],i),j)
    right=step(step(at[key],j),i)
    target=tuple(key[k]+int(k in ('xyz'.index(i),'xyz'.index(j))) for k in range(3))
    assert left==right==at[target]
    face+=1
   terminals=[]
   for order in permutations('xyz'):
    st=at[(0,0,0)]
    for axis in order:st=step(st,axis)
    assert st==at[(1,1,1)]
    terminals.append(st);paths+=1
   assert len(set(terminals))==1
   assert D(unchart(terminals[0])[3])==R(p)
   if counter is None and P(R(p))!=R(P(p)):counter=p
   count+=1
assert (count,face,paths,points)==(5832,34992,34992,52488)
assert counter is not None
print('SymPy',s.__version__)
print('PASS',count,'pivot02 inverse states;',8*count,'vertex chart roundtrips')
print('PASS',face,'genuine transported faces;',paths,'terminal paths;',points,'5D point comparisons')
print('PASS noncommuting raw pivot/rotation witness',counter)
