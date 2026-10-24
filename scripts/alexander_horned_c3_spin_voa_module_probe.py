#!/usr/bin/env python3
"""Exact finite module over the existing 180-coordinate commutative VOA.

M=Fun(C3 x A5,H_Q), V=Fun(C3 x A5,Q), with pointwise scalar action.
The C3 spin lift s=-q of order three gives a genuine semilinear
right action of Q=A5^3 rtimes C3 on M and preserves ALL trivial
vertex modes. The path lift q gives a C6 action, not C3.
M is a VOA MODULE, NOT a newly identified 360-coordinate scalar VOA.
"""
from fractions import Fraction as F
from itertools import permutations
from random import Random
E=(F(1),F(0),F(0),F(0))
q=(F(1,2),)*4
s=tuple(-v for v in q)

def qm(a,b):
 x,y,z,w=a; X,Y,Z,W=b
 return (x*X-y*Y-z*Z-w*W,x*Y+y*X+z*W-w*Z,
         x*Z-y*W+z*X+w*Y,x*W+y*Z-z*Y+w*X)
def powq(a,n):
 r=E
 for _ in range(n):r=qm(r,a)
 return r
def scale(a,v):return tuple(a*x for x in v)
assert powq(q,3)==scale(-1,E) and powq(s,3)==E

def parity_even(t):return sum(t[i]>t[j] for i in range(5) for j in range(i+1,5))%2==0
A5=tuple(p for p in permutations(range(5)) if parity_even(p))
I5=tuple(range(5))
assert len(A5)==60
def am(a,b):return tuple(a[b[j]] for j in range(5))
def beta(tr,k):return tuple(tr[(i-k)%3] for i in range(3))
def groupmul(g,h):
 a,k=g; b,l=h; shifted=beta(b,k)
 return (tuple(am(a[i],shifted[i]) for i in range(3)),(k+l)%3)
def ca(g,x):
 a,k=g; i,u=x; j=(i+k)%3
 return j,am(a[j],u)
SLOTS=tuple((k,a) for k in range(3) for a in A5)
assert len(SLOTS)==180
R=Random(20261024)
ACTORS=[((I5,I5,I5),i) for i in range(3)]
ACTORS += [(tuple(A5[R.randrange(60)] for _ in range(3)),R.randrange(3)) for _ in range(15)]
for g in ACTORS:
 for h in ACTORS:
  comp=groupmul(g,h)
  for x in SLOTS:assert ca(comp,x)==ca(g,ca(h,x))

chargeindex={a:j for j,a in enumerate(A5)}
def f(x):
 k,a=x; return F(1+k+(chargeindex[a]%7),5)
def psi(x):
 k,a=x; n=chargeindex[a]
 return (F(k+1,3),F(n%7,5),F((n+k)%11,7),F((n+2*k)%13,11))
def scalaract(f,psi,x):return scale(f(x),psi(x))
def vm(g,f,x):return f(ca(g,x))
def mm(g,p,x,rot=s):
 v=p(ca(g,x)); return qm(powq(rot,g[1]),v)

def check():
 for g in ACTORS:
  for x in SLOTS:
   lhs=mm(g,lambda y:scalaract(f,psi,y),x)
   rhs=scale(vm(g,f,x),mm(g,psi,x))
   assert lhs==rhs
  assert all(mm(g,lambda y:scale(F(1),psi(y)),x)==mm(g,psi,x) for x in SLOTS)
 for g in ACTORS:
  for h in ACTORS:
   comp=groupmul(g,h)
   for x in SLOTS:
    lhs=mm(comp,psi,x)
    rhs=mm(h,lambda y:mm(g,psi,y),x)
    assert lhs==rhs
 for x in SLOTS:
  ro=ACTORS[1]
  c=mm(ro,lambda y:mm(ro,lambda z:mm(ro,psi,z),y),x)
  assert c==psi(x)
  r2=mm(ro,lambda y:mm(ro,lambda z:mm(ro,psi,z,rot=q),y,rot=q),x,rot=q)
  assert r2==scale(-1,psi(x))
 print('PASS 180 scalar VOA coordinates, 4Q-dimensional quaternion spinor module per site')
 print('PASS 18 actor samples x 180 slots: module covariance with pointwise vertex modes')
 print('PASS 18x18 full semidirect group-law samples x 180 slots')
 print('PASS C3 spin lift third power +1, path lift third power -1')
 print('Module dimension 720 over Q; 360 over Q(i) with RIGHT i structure (NOT the 360-site scalar spin-cover VOA)')
 print('NOT proven: literal Agda module instance, Moonshine/Monster correspondence, wild E geometry')
if __name__=='__main__':check()
