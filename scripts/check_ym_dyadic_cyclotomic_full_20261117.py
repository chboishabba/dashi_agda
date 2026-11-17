#!/usr/bin/env python3
"""Exact dyadic S3 product cubature in cyclotomic Q[z]/(z^N+1).
No trigonometric floating point, Machin pi, or polynomial roots.
This is a finite computational reference, not Agda kernel acceptance.
Fejer/Stroud/Pizzetti-Folland and original DASHI source attribution.
"""
from fractions import Fraction as Q
from math import prod
from functools import lru_cache
class Ring:
 def __init__(self,N,d=0):
  self.N=N
  self.d={k:Q(v) for k,v in d.items() if v} if isinstance(d,dict) else ({0:Q(d)} if d else {})
 def __add__(self,o):
  if not isinstance(o,Ring):o=Ring(self.N,o)
  assert self.N==o.N
  d=self.d.copy()
  for k,v in o.d.items():d[k]=d.get(k,Q(0))+v
  return Ring(self.N,d)
 __radd__=__add__
 def __neg__(self):return Ring(self.N,{k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+(-o if isinstance(o,Ring) else -Q(o))
 def __rsub__(self,o):return Ring(self.N,o)-self
 def __mul__(self,o):
  if not isinstance(o,Ring):return Ring(self.N,{k:v*o for k,v in self.d.items()})
  assert self.N==o.N
  d={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    u,r=divmod(k+j,self.N)
    d[r]=d.get(r,Q(0))+v*w*(-1 if u%2 else 1)
  return Ring(self.N,d)
 __rmul__=__mul__
 def __pow__(self,k):
  assert k>=0
  out=Ring(self.N,1);p=self
  while k:
   if k%2:out=out*p
   p=p*p;k//=2
  return out
 def rational(self):
  assert all(v==0 for k,v in self.d.items() if k),self.d
  return self.d.get(0,Q(0))
def power(N,k):
 u,r=divmod(k,N)
 return Ring(N,{r:Q(-1 if u%2 else 1)})
def cos(N,k):return (power(N,k)+power(N,-k))*Q(1,2)
def sin(N,k):return -power(N,N//2)*(power(N,k)-power(N,-k))*Q(1,2)
def poch(x,k):
 out=Q(1)
 for j in range(k):out*=x+j
 return out
def H(e):
 if any(x%2 for x in e):return Q(0)
 return prod(poch(Q(1,2),x//2) for x in e)/poch(Q(2),sum(e)//2)
def orders(d):
 r=1
 while 2*((1<<r)-1)-1<d:r+=1
 s=1
 while (1<<s)<=d:s+=1
 return (1<<r,1<<s,1<<s)
@lru_cache(None)
def cheb(A,a,k):
 # Cheb-II weight: 2/A * sin^2(pi j/A); all integrands polynomial.
 out=Ring(A)
 for j in range(1,A):
  x=cos(A,j)
  out=out+x**a*(1-x*x)**(k+1)
 return (Q(2,A)*out).rational()
@lru_cache(None)
def fejer(M,b,k):
 # Normalized Fejer-I weight for dt/2 (not the dt weight).
 out=Ring(2*M)
 for j in range(1,M+1):
  theta=2*j-1
  x=cos(2*M,theta)
  weight=Ring(2*M,1)
  for h in range(1,(M-1)//2+1):
   weight=weight-Q(2,4*h*h-1)*cos(2*M,2*h*theta)
  out=out+weight*x**b*(1-x*x)**k
 return (out*Q(1,M)).rational()
@lru_cache(None)
def circle(L,c,d):
 out=Ring(L)
 for j in range(L):
  x=cos(L,2*j);y=sin(L,2*j)
  out=out+x**c*y**d
 return (out*Q(1,L)).rational()
def monomials(d):
 for a in range(d+1):
  for b in range(d+1-a):
   for c in range(d+1-a-b):
    for e in range(d+1-a-b-c):yield(a,b,c,e)
checks=0
for d in (3,5,7,9):
 A,M,L=orders(d)
 assert all((x&(x-1))==0 for x in (A,M,L))
 for c in range(d+1):
  for e in range(d+1-c):
   if c%2 or e%2:assert circle(L,c,e)==0;checks+=1
 for b in range(1,d+1,2):
  for k in range((d-b)//2+1):
   assert fejer(M,b,k)==0;checks+=1
 for a in range(1,d+1,2):
  for k in range((d-a)//2+1):
   assert cheb(A,a,k)==0;checks+=1
 assert cheb(A,0,0)==fejer(M,0,0)==circle(L,0,0)==1
 checks+=3
 n=0
 for a,b,c,e in monomials(d):
  if any(x%2 for x in (a,b,c,e)):h=Q(0)
  else:
   u=(c+e)//2;v=(b+c+e)//2
   h=cheb(A,a,v)*fejer(M,b,u)*circle(L,c,e)
  assert h==H((a,b,c,e)),(d,(a,b,c,e),h,H((a,b,c,e)))
  checks+=1;n+=1
 print(f"degree={d} nodes={(A-1)*M*L} monomials={n}")
print("DYADIC_CYCLOTOMIC_ALL_MONOMIALS_PASS",checks)
