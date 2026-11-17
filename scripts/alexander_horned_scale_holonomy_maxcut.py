#!/usr/bin/env python3
"""Exact Hatcher finite-X_n / tame-B_n / ideal-B observable discriminator.

Primary sources: Hatcher Algebraic Topology Ex 2B.2; Alexander 1924;
Maschke and finite perfect group basics; Grillet Bridges 2022 physical
4-level model. This code tests finite ALGEBRA, not a physical device or
wild-ball embedding. See docs/topology roadmap for the three lanes.
"""
from itertools import product
from fractions import Fraction as F
E=(1,0,0,1);N=(4,0,0,4)
def mul(a,b):
 x,y,z,w=a;X,Y,Z,W=b
 return ((x*X+y*Z)%5,(x*Y+y*W)%5,(z*X+w*Z)%5,(z*Y+w*W)%5)
def inv(x):
 a,b,c,d=x
 return (d%5,-b%5,-c%5,a%5)
def comm(a,b):return mul(mul(mul(a,b),inv(a)),inv(b))
def power(a,n):
 y=E
 for _ in range(n):y=mul(y,a)
 return y
def generated(gs):
 seen={E};todo=[E]
 while todo:
  v=todo.pop()
  for g in gs:
   w=mul(v,g)
   if w not in seen:seen.add(w);todo.append(w)
 return seen
S=tuple((a,b,c,d) for a,b,c,d in product(range(5),repeat=4)
        if (a*d-b*c)%5==1)
assert len(S)==120
section={};root=None;q8=None
for a in S:
 for b in S:
  g=comm(a,b)
  section.setdefault(g,(a,b))
  if g==N and q8 is None and len(generated((a,b)))==8:q8=(a,b)
  if power(g,3)==N and root is None and len(generated((a,b)))==120:
   root=(g,a,b)
assert len(section)==120 and root is not None and q8 is not None
assert {comm(a,b) for a in generated(q8) for b in generated(q8)}=={E,N}
assert all(x not in (E,N) for x in q8)
print("PASS Q8 gives one commutator -I but cannot lift noncentral child labels")
q,a,b=root
assert comm(a,b)==q and power(q,3)==N
def word_reduce(w):
 out=[]
 for x in w:
  if out and out[-1]==-x:out.pop()
  else:out.append(x)
 return tuple(out)
def expand(word,n):
 m=1<<n;out=[]
 for x in word:
  c,i=divmod(abs(x)-1,m)
  assert c<3
  u=2*c*m+2*i+1;v=u+1
  out.extend((u,v,-u,-v) if x>0 else (v,u,-v,-u))
 return word_reduce(out)
def expvector(word,r):
 v=[0]*r
 for x in word:v[abs(x)-1]+=1 if x>0 else -1
 return tuple(v)
for n in range(7):
 rank=3*(1<<n)
 for x in range(1,rank+1):
  w=expand((x,),n)
  assert len(w)==4 and expvector(w,2*rank)==(0,)*(2*rank)
 print(f"PASS H1(F_{rank}) -> H1(F_{rank*2}) is ZERO for all generators")
levels=[{():q}]
for n in range(7):
 nxt={}
 for address,g in levels[-1].items():
  x,y=(a,b) if not address else section[g]
  assert comm(x,y)==g
  nxt[address+(0,)]=x;nxt[address+(1,)]=y
 levels.append(nxt)
assert power(levels[0][()],3)==N
print("PASS compatible nonabelian 2I quotient through 7 binary refinements")
print("PASS root cube maps to central -I; ordinary SU2 trace -2 vs +2")
print("Mathematical limit: H1(G_A*G_A*G_A)=0, pi1 != 1")
print("Contrast: finite tame B_n exterior pi1=1; enclosing X_n exterior F_(3*2^n)")
print("n,three_sector_handles,nominal_mm_at_200mm_scale_0.43")
for n in range(10):
 print(n,3*(1<<n),round(float(F(200)*F(43,100)**n),6),sep=",")
print("No physical wild ball, no measured holonomy, no kernel receipt claimed")
