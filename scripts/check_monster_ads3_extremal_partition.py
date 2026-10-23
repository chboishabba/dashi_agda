#!/usr/bin/env python3
"""Exact low-q Monster partition function coefficients from E4^3/Delta.
Independent integer arithmetic up to q^3; comparison to Witten AdS3
extremal CFT hypothesis is conditional, not an AdS/CFT proof.
"""
from fractions import Fraction

N=7
def mul(a,b):
 o=[0]*(N+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):
   if i+j<=N:o[i+j]+=x*y
 return o
def div(a,b):
 assert b[0]==1
 o=[0]*(N+1)
 for n in range(N+1):
  o[n]=a[n]-sum(b[k]*o[n-k] for k in range(1,n+1))
 return o
E4=[1]+[240*sum(d**3 for d in range(1,n+1) if n%d==0) for n in range(1,N+1)]
# Delta /q = product (1-q^n)^24, exact integers.
D=[1]+[0]*N
from math import comb
for n in range(1,N+1):
 f=[0]*(N+1)
 for k in range(min(24,N//n)+1):f[k*n]=(-1)**k*comb(24,k)
 D=mul(D,f)
j_shift=div(mul(mul(E4,E4),E4),D) # j=q^-1 * j_shift
assert j_shift[:4]==[1,744,196884,21493760],j_shift[:4]
J=[j_shift[0],j_shift[1]-744,*j_shift[2:]]
assert J[:4]==[1,0,196884,21493760]
assert J[2]==1+196883
# J coefficients interpreted with exponent -1,0,1,2,...
print("PASS J=j-744: q^-1 + 196884 q + 21493760 q^2 + ...")
print("PASS 196884=1+196883")
print("BOUNDARY c=24 Monster CFT is known; pure AdS3 quantum gravity dual is conjectural")
