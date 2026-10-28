#!/usr/bin/env python3
"""Exact CRT 2^a*3^b horn coordinates and p=2,3 congruence audit."""
from itertools import product
from math import gcd

def crt(a,d,b,e):
 assert gcd(d,e)==1 and 0<=a<d and 0<=b<e
 x=a+d*((b-a)*pow(d,-1,e)%e)
 assert 0<=x<d*e and x%d==a and x%e==b
 return x

def multiply(x,y,p):
 a,b,c,d=x;A,B,C,D=y
 return ((a*A+b*C)%p,(a*B+b*D)%p,(c*A+d*C)%p,(c*B+d*D)%p)

def inverse(x,p):
 a,b,c,d=x
 z=pow((a*d-b*c)%p,-1,p)
 return ((d*z)%p,(-b*z)%p,(-c*z)%p,(a*z)%p)

def derived(p):
 G={(a,b,c,d) for a,b,c,d in product(range(p),repeat=4)
    if (a*d-b*c)%p!=0}
 sizes=[len(G)];unit=(1,0,0,1)
 while len(G)>1:
  comms={multiply(multiply(multiply(a,b,p),inverse(a,p),p),inverse(b,p),p)
         for a in G for b in G}
  steps=comms|{inverse(x,p) for x in comms}
  nextG={unit};front=[unit]
  while front:
   x=front.pop()
   for g in steps:
    y=multiply(x,g,p)
    if y not in nextG:nextG.add(y);front.append(y)
  assert len(nextG)<len(G)
  G=nextG;sizes.append(len(G))
 return sizes

count=0
for n in range(11):
 d=2**n
 for b,c in product(range(d),range(3)):
  x=crt(b,d,c,3)
  assert crt(b,d,(c+1)%3,3)%d==b
  if n:assert x%(3*(d//2))==crt(b%(d//2),d//2,c,3)
  count+=1
for a,k in product(range(1,5),repeat=2):
 d,e=2**a,3**k
 for x in range(d*e):
  assert crt(x%d,d,x%e,e)==x
assert derived(2)==[6,3,1]
assert derived(3)==[48,24,8,2,1]
print('PASS CRT binary horn x C3 -> mod (3*2^n), n0..10:',count,'states')
print('PASS general mixed CRT 2^a*3^b, a,b 1..4; inverse exact')
print('PASS GL2(F2) derived [6,3,1], GL2(F3) derived [48,24,8,2,1]')
print('Mathematical implication: perfect G -> GL2(Z2), GL2(Z3) trivial')
print('NOT certified: Agda kernel, geometry or full p-adic field construction')
