#!/usr/bin/env python3
"""Exact Monster c=24 character -> Virasoro-primary multiplicity, low grades.
Assumes irreducible generic c=24 nonvacuum Verma characters and
vacuum null L_-1|0>. Checks integer formal series, not AdS3 duality.
"""
from math import comb
N=8
def mul(a,b):
 z=[0]*(N+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):
   if i+j<=N:z[i+j]+=x*y
 return z
def quotient(a,b):
 assert b[0]==1
 z=[0]*(N+1)
 for k in range(N+1):z[k]=a[k]-sum(b[j]*z[k-j] for j in range(1,k+1))
 return z
E4=[1]+[240*sum(d**3 for d in range(1,n+1) if n%d==0) for n in range(1,N+1)]
delta=[1]+[0]*N
euler=[1]+[0]*N
for n in range(1,N+1):
 term=[0]*(N+1);term[0]=1;term[n]=-1;euler=mul(euler,term)
 pow24=[0]*(N+1)
 for j in range(min(24,N//n)+1):pow24[n*j]=(-1)**j*comb(24,j)
 delta=mul(delta,pow24)
jshift=quotient(mul(mul(E4,E4),E4),delta)
assert jshift[:4]==[1,744,196884,21493760]
# J(q)=q^-1*(1 + 0*q + 196884*q^2+...).
Jshift=jshift[:];Jshift[1]-=744
primary_shift=mul(Jshift,euler)
# Remove vacuum character q^-1*(1-q)/prod_{n>=1}(1-q^n).
primary_shift[0]-=1
primary_shift[1]+=1
assert primary_shift[0]==primary_shift[1]==0
assert primary_shift[2]==196883,primary_shift
assert all(x>=0 for x in primary_shift[:N-1]),primary_shift
print('PASS graded J: 196884 states at weight 2')
print('PASS Virasoro primary at weight 2: 196883 (vacuum L_-2 descendant removed)')
print('PASS nonnegative formal primary counts through weight',N-2)
print('Primary multiplicities weight 2..5:',primary_shift[2:6])
print('ASSUMES generic c24 Virasoro character decomposition; no AdS3 gravity proof')
