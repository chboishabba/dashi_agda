#!/usr/bin/env python3
"""Exact finite C3 spin lift / cocycle steelman.

At the real spatial 120-degree rotor q=(1+i+j+k)/2,
q**3=-1 and q**6=1.  A genuine group hom C3->Spin3
sending generator to q cannot exist; sending to -q works.

The path-selected set section {1,q,q^2} has a nonzero
central 2-cocycle, but it is an exact COBoundary.
This is consistent with H^2(C3,C2)=0, without proving a
continuous spin-bundle lift on a wild manifold.
"""
from fractions import Fraction as F
from itertools import product

ONE=(F(1),F(0),F(0),F(0))
NEG=(-F(1),F(0),F(0),F(0))
HALF=F(1,2)
q=(HALF,)*4
qm=(HALF,-HALF,-HALF,-HALF)
other=tuple(-x for x in q)

def mult(a,b):
 x,y,z,w=a
 X,Y,Z,W=b
 return (x*X-y*Y-z*Z-w*W,x*Y+y*X+z*W-w*Z,
         x*Z-y*W+z*X+w*Y,x*W+y*Z-z*Y+w*X)
def powq(a,n):
 r=ONE
 for _ in range(n): r=mult(r,a)
 return r
def conjugate(a,v):
 return mult(mult(a,v),qm)
def scalar(s):
 return ONE if s==0 else NEG
def lift(i,s):
 return mult(powq(other,i),scalar(s))
def Lmult(a,b):
 return ((a[0]+b[0])%3,(a[1]+b[1])%2)
def phasesection(i):
 return powq(q,i)
def cocycle(i,j):
 return (i+j)//3
def coboundary_sign(i):
 return i%2  # +,-,+ for i=0,1,2

def check():
 assert powq(q,3)==NEG and powq(q,6)==ONE
 assert powq(other,3)==ONE
 assert mult(q,qm)==mult(qm,q)==ONE
 assert len({lift(i,s) for i,s in product(range(3),range(2))})==6
 assert lift(1,1)==q and lift(1,0)==other
 for a,b,c in product(range(3),repeat=3):
  assert (a+b+c)%3 == (a+(b+c)%3)%3
 for a,b in product(product(range(3),range(2)),repeat=2):
  assert mult(lift(*a),lift(*b))==lift(*Lmult(a,b))
  assert (Lmult(a,b))[0]==(a[0]+b[0])%3
 for i,j in product(range(3), repeat=2):
  raw=mult(phasesection(i),phasesection(j))
  endpoint=phasesection((i+j)%3)
  assert raw==mult(scalar(cocycle(i,j)),endpoint)
  assert mult(scalar(coboundary_sign(i)),
              mult(scalar(coboundary_sign(j)),
                   scalar(coboundary_sign((i+j)%3))))==scalar(cocycle(i,j))
  assert mult(scalar(coboundary_sign(i)),phasesection(i))==powq(other,i)
 assert sum(cocycle(i,j) for i,j in product(range(3),repeat=2))==3
 assert [a for a in (q,other) if powq(a,3)==ONE]==[other]
 # Genuine action of abstract C3 on spinor signs, path q only
 # defines an action of its order-six cover.
 for i,j in product(range(3),repeat=2):
  assert mult(powq(other,i),powq(other,j))==powq(other,(i+j)%3)
 assert powq(q,3)!=ONE
 # Same spatial transformation on arbitrary rational pure quaternion:
 for x,y,z in product(range(-3,4),repeat=3):
  pure=(F(0),F(x),F(y),F(z))
  target=(F(0),F(z),F(x),F(y))
  assert conjugate(q,pure)==target
  assert mult(mult(other,pure),tuple(-k for k in qm))==target
 print("PASS 6-element spin preimage = C3 x C2 = C6; exact 6x6 product")
 print("PASS chosen path rotor q^3=-1; coherent rotor (-q)^3=+1")
 print("PASS central path cocycle=carry with 3 negatives; all 9 values coboundary")
 print("PASS unique C3 homomorphic generator lift among the two signed preimages")
 print("PASS same ambient xyz->(z,x,y), 343 exact rational coordinate triples")
 print("NOT tested: continuous path-lift in SU2 or equivariant wild-complement spin bundle")
if __name__=="__main__": check()
