#!/usr/bin/env python3
"""Source-specific Griess M81/243/240 actual-actor regression, no helper imports.

Original: R. L. Griess Jr., J. Algebra 131 (1990), 281-293,
DOI 10.1016/0021-8693(90)90176-O. Reuse PRIOR DASHI
T5-relative/finite E6 and Griess chart mathematical roots.
The explicit finite checker is NOT a Lean/Agda kernel certificate.
"""
from itertools import product
from collections import Counter
from sympy.combinatorics import Permutation, PermutationGroup

V=list(product(range(3),repeat=3))
M81=list(product(V,range(3)))
idx={m:i for i,m in enumerate(M81)}
def add(x,y):return tuple((u+v)%3 for u,v in zip(x,y))
def g(x,y):
    a,b,c=x;p,q,r=y
    return (-a*b*r-c*p*q+b*c*p+a*q*r)%3
def mul(a,b):
    return (add(a[0],b[0]),(a[1]+b[1]+g(a[0],b[0]))%3)
def shear(x,i,j):
    y=list(x);y[i]=(y[i]+y[j])%3
    return tuple(y)
def h(x,i,j):
    a,b,c=x
    return {(0,1):c*(1-b*b),(0,2):0,
      (1,0):c*(1-a*a),(1,2):a*(c*c-1),
      (2,0):0,(2,1):a*(b*b-1)}[i,j]%3
def lift(m,i,j):
    x,t=m
    return shear(x,i,j),(t+h(x,i,j))%3

gens=[]
for i in range(3):
 for j in range(3):
  if i==j:continue
  for x,y in product(V,repeat=2):
   lhs=(h(add(x,y),i,j)-h(x,i,j)-h(y,i,j))%3
   rhs=(g(shear(x,i,j),shear(y,i,j))-g(x,y))%3
   assert lhs==rhs,(i,j,x,y)
  for a,b in product(M81,repeat=2):
   assert lift(mul(a,b),i,j)==mul(lift(a,i,j),lift(b,i,j))
  assert all(lift(lift(lift(m,i,j),i,j),i,j)==m for m in M81)
  P=Permutation([idx[lift(m,i,j)] for m in M81])
  assert P**3==Permutation(80)
  gens.append(P)
G=PermutationGroup(gens)
assert G.order()==151632
assert sorted(map(len,G.orbits()))==[1,1,1,78]
def shift(m,lam):
 x,t=m
 return x,(t+sum(lam[k]*x[k] for k in range(3)))%3
for lam in V:
 assert G.contains(Permutation([idx[shift(m,lam)] for m in M81]))
assert len({tuple(idx[shift(m,l)] for m in M81) for l in V})==27

T5=list(product(range(3),repeat=5))
diag={(t,)*5 for t in range(3)}
def chart(z):
 return ((tuple((z[k]-z[4])%3 for k in range(3)),
          (z[3]-z[4])%3),z[4])
def unchart(m,t):
 x,a=m
 return tuple((x[k]+t)%3 for k in range(3))+((a+t)%3,t)
assert all(unchart(*chart(z))==z for z in T5)
assert {chart(z) for z in T5}==set(product(M81,range(3)))
assert all((z in diag)==(chart(z)[0]==((0,0,0),0)) for z in T5)
old240=[z for z in T5 if z not in diag]
assert len(old240)==240
assert Counter('noncentral' if chart(z)[0][0]!=(0,0,0)
               else 'central' for z in old240)=={
               'noncentral':234,'central':6}
q=lambda z:sum(u*u for u in z)%3
assert Counter(map(q,T5))=={0:81,1:90,2:72}
assert Counter(map(q,diag))=={0:1,2:2}
assert Counter(map(q,old240))=={0:80,1:90,2:70}
for z in T5:
 m,t=chart(z);w=(*m[0],m[1])
 assert q(z)==(sum(a*a for a in w)+2*t*sum(w)+2*t*t)%3
for i in range(3):
 for j in range(3):
  if i==j:continue
  for z in old240:
   m,t=chart(z)
   acted=unchart(lift(m,i,j),t)
   assert acted in old240 and chart(acted)==(lift(m,i,j),t)
x,y=(0,0,1),(0,1,0)
assert g(shear(x,0,1),shear(y,0,1))==2 and g(x,y)==0
print('PASS source phase cocycles 4374/4374; M81 products 39366/39366')
print('PASS 6 order-three lifts; G<=Sym(81) order151632, character kernel27')
print('PASS M81 orbits 1+1+1+78; old240 transported six fixed + three 78-orbits')
print('PASS original T5=243 and diagonal-removed 240 reciprocal chart; 6+234 split')
print('PASS old E6 quadratic strata 243=81+90+72, relative 240=80+90+70')
print('OPEN Lean/Agda kernel, SL3 splitting, E8/full-Weyl and physical intertwiners')
