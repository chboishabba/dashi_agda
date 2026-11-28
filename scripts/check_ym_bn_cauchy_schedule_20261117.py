#!/usr/bin/env python3
"""Exact rational b_n Pochhammer moments and effective fast-Cauchy schedule.
A POSITIVE cubature exact through n+1 and admissible bounded UC f is still
required in the Agda source: this script does NOT inhabit those theorems.
"""
from fractions import Fraction as Q
from math import comb
assertions=0
def check(x,y):
 global assertions
 assert x==y,(x,y)
 assertions+=1
def poch(x,n):
 for j in range(n):x*=1 if False else 1
 return x
def rising(x,n):
 y=Q(1)
 for j in range(n):y*=x+j
 return y
def Ht(k):
 if k%2:return Q(0)
 return rising(Q(1,2),k//2)/rising(Q(2),k//2)
def Hbn(n,shift=0):
 return sum((Q(comb(n,j),2**n)*Ht(j+shift)
             for j in range(n+1)),Q(0))
for n in range(101):
 c=Hbn(n)
 check(c,rising(Q(3,2),n)/rising(Q(3),n))
 check((c-Hbn(n,1))/c,Q(3,n+3))
 check(Hbn(n,1)/c,Q(n,n+3))
 check(Hbn(n,2)/c,Q(n*n+n+3,(n+3)*(n+4)))
def schedule(k,bound,lip):
 eps=Q(1,2**(k+3))
 delta=eps/(2*lip)
 n=int((Q(96)*bound*lip**2/eps**3).__ceil__())
 return n,eps,delta
for bound,lip in ((Q(1),Q(1)),(Q(3,2),Q(7,4)),(Q(5),Q(1,3))):
 for k in range(7):
  n,eps,delta=schedule(k,bound,lip)
  check(lip*delta,eps/2)
  assert Q(12)*bound/((n+3)*delta**2)<=eps/2
  assertions+=1
  for j in range(k,7):
   nj,ej,dj=schedule(j,bound,lip)
   assert eps+ej<=Q(1,2**(k+2))
   assertions+=1
 print(f"bound={bound} lip={lip}: n0={schedule(0,bound,lip)[0]} n6={schedule(6,bound,lip)[0]}")
print(f"EXACT_BN_CAUCHY_SCHEDULE_PASS={assertions}")
