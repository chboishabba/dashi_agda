#!/usr/bin/env python3
"""Exact same-object Gaussian-rational C3 spin/cyclotomic intertwiner.

Source donor: CayleyDicksonRationalComplexQuaternionExact and
AlexanderHornedQuaternionC3SpinExact. Mathematical claim: the
coherent rotor V=U(-(1+i+j+k)/2) satisfies V*T=T*A for
A=[[0,-1],[1,-1]], with T inverse explicitly. Also checks reductions
modulo 3,5,7, where 1/2 is defined. NOT a Dirac eigenmode.
"""
from fractions import Fraction as F
from itertools import product
def add(a,b,p=None):return tuple((x+y)%p if p else x+y for x,y in zip(a,b))
def mul(a,b,p=None):
 x,y=a;u,v=b;w=x*u-y*v;z=x*v+y*u
 return (w%p,z%p) if p else (w,z)
def mm(A,B,p=None):
 return tuple(tuple(add(mul(A[i][0],B[0][j],p),mul(A[i][1],B[1][j],p),p)
                    for j in range(2)) for i in range(2))
def mv(A,v,p=None):
 return tuple(add(mul(A[i][0],v[0],p),mul(A[i][1],v[1],p),p) for i in range(2))
def test(p=None):
 h=pow(2,-1,p) if p else F(1,2)
 def c(x,y=0):return (x%p,y%p) if p else (F(x),F(y))
 one,zero=c(1),c(0);a=c(-h,-h);b=c(h,-h);d=c(-h,h)
 V=((a,a),(b,d))
 T=((one,a),(zero,b))
 Ti=((one,c(0,1)),(zero,c(1,1)))
 A=((zero,c(-1)),(one,c(-1)))
 I=((one,zero),(zero,one))
 assert mm(V,T,p)==mm(T,A,p)
 assert mm(T,Ti,p)==mm(Ti,T,p)==I
 assert mm(mm(V,V,p),V,p)==I
 assert mm(mm(A,A,p),A,p)==I
 assert mul(b,c(1,1),p)==one
 for x,y,z,w in product(range(3),repeat=4):
  v=(c(x,y),c(z,w))
  assert mv(V,mv(T,v,p),p)==mv(T,mv(A,v,p),p)
  assert mv(Ti,mv(T,v,p),p)==v
for p in (None,3,5,7):
 test(p)
 print('PASS exact Q(i) intertwiner' if p is None else f'PASS mod {p} reduction')
print('NO physical Dirac zero-mode or spin bundle claimed')
