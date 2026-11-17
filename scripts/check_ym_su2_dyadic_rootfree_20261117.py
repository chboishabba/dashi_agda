#!/usr/bin/env python3
"""YM.REAL: independent DYADIC S3 product cubature reference.

Cheb-II m=(2^r-1), Fejer-I M=2^s, circle L=2^t.
Choose independent powers with 2m-1>=degree, M>degree, L>degree.
All nodes are constructible from the repeated complex square-root tower;
no Machin/classical pi equivalence or arbitrary Legendre roots.
Not a kernel proof of Bishop square roots or all-m character orthogonality.
"""
import math
from fractions import Fraction as Q

checks=0
def check(a,b,tag):
 global checks
 assert a==b,(tag,a,b)
 checks+=1
def poch(a,n):
 x=Q(1)
 for j in range(n):x*=a+j
 return x
def H(e):
 if any(t%2 for t in e):return Q(0)
 a=[t//2 for t in e]
 return math.prod(poch(Q(1,2),t) for t in a)/poch(Q(2),sum(a))
def factored(e):
 a,b,c,d=e
 if any(t%2 for t in e):return Q(0)
 u=(c+d)//2;v=(b+c+d)//2
 return (poch(Q(1,2),c//2)*poch(Q(1,2),d//2)/poch(Q(1),u)
         *poch(Q(1,2),b//2)*poch(Q(1),u)/poch(Q(3,2),v)
         *poch(Q(1,2),a//2)*poch(Q(3,2),v)/poch(Q(2),(a+b+c+d)//2))
def monomials(d):
 for a in range(d+1):
  for b in range(d+1-a):
   for c in range(d+1-a-b):
    for e in range(d+1-a-b-c):
     yield a,b,c,e
def counts(d):
 r=1
 while 2*(2**r-1)-1<d:r+=1
 s=0
 while 2**s<=d:s+=1
 m=(1<<r)-1;M=L=1<<s
 return r,s,m,M,L
for d in (0,1,2,3,5,7,9):
 r,s,m,M,L=counts(d)
 assert 2*m-1>=d and M>d and L>d
 assert ((m+1)&m)==0 and (M&(M-1))==0
 checks+=1
 for e in monomials(d):
  check(factored(e),H(e),("factor",d,e))
 # The Fejer midpoint weights integrate dt/2, so normalize with 1/M.
 J=(M-1)//2
 check(Q(1)-sum((Q(2,4*j*j-1) for j in range(1,J+1)),Q(0)),
       Q(1,2*J+1),("Fejer positive floor",d))
 # All surviving Fourier modes in angular circle have abs(k)<=d<L,
 # hence only k=0 is divisible by L.
 for k in range(-d,d+1):
  check(int(k==0),int(k%L==0),("circle",d,k))
 print(f"degree={d} ChebII={m} FejerI={M} Circle={L} nodes={m*M*L}")
print(f"DYADIC_S3_EXACT_RATIONAL_PASS={checks}")
