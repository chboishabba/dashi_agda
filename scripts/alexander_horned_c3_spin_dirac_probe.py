#!/usr/bin/env python3
"""Exact Gaussian-rational Pauli/Dirac covariance of the horn C3 rotor.

Finite algebraic result only. On any C3-invariant open E subset R^3,
T psi(x)=U(-q) psi(R^{-1}x) defines a genuine action of C3 on
compactly supported 2-spinors and commutes with the flat Dirac operator.
This calculation verifies the principal-symbol/chain-rule coefficients.
It does NOT construct the wild embedding E, boundary conditions, a
self-adjoint Dirac realization, a Monster VOA or a geometric pi1 lift.
"""
from fractions import Fraction as F
from itertools import product

def g(x=0,y=0):return (F(x),F(y))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(k,a):return (F(k)*a[0],F(k)*a[1])
ZERO=g();ONE=g(1);IM=g(0,1)
def M(a,b,c,d):return (a,b,c,d)
MID=M(ONE,ZERO,ZERO,ONE)
MZERO=M(ZERO,ZERO,ZERO,ZERO)
def mm(A,B):
 a,b,c,d=A; x,y,z,w=B
 return M(add(mul(a,x),mul(b,z)),add(mul(a,y),mul(b,w)),
          add(mul(c,x),mul(d,z)),add(mul(c,y),mul(d,w)))
def madd(A,B):return tuple(add(x,y) for x,y in zip(A,B))
def mscale(k,A):return tuple(scale(k,x) for x in A)
def mpow(A,n):
 out=MID
 for _ in range(n):out=mm(out,A)
 return out

def quaternion(a,b,c,d):
 # exact faithful quaternion map to SU(2) for unit quaternion inputs
 return M(add(g(a),scale(b,IM)),add(g(c),scale(d,IM)),
          add(neg(g(c)),scale(d,IM)),add(g(a),neg(scale(b,IM))))
h=F(1,2)
U=quaternion(h,h,h,h)
Uinv=quaternion(h,-h,-h,-h)
V=mscale(-1,U)
Vinv=mscale(-1,Uinv)
P=[quaternion(0,1,0,0),quaternion(0,0,1,0),quaternion(0,0,0,1)]
R=((0,0,1),(1,0,0),(0,1,0))  # (x,y,z)->(z,x,y)
Rinv=tuple(zip(*R))

def verify():
 assert mm(U,Uinv)==mm(Uinv,U)==MID
 assert mpow(U,3)==mscale(-1,MID)
 assert mpow(U,6)==MID and mpow(V,3)==MID
 assert U!=V and all(mm(mm(V,P[j]),Vinv)==P[(j+1)%3] for j in range(3))
 assert all(mm(mm(U,P[j]),Uinv)==P[(j+1)%3] for j in range(3))
 for j in range(3):
  # D=sum_i P_i d_i. Chain rule for Tpsi(x)=V psi(R^-1 x):
  # sum_i (R^-1)_{ji} P_i V == V P_j.
  lhs=MZERO
  for i in range(3): lhs=madd(lhs,mscale(Rinv[j][i],mm(P[i],V)))
  assert lhs==mm(V,P[j])
 for i,j in product(range(3),repeat=2):
  assert mpow(V,(i+j)%3)==mm(mpow(V,i),mpow(V,j))
 def rotate(x):return (x[2],x[0],x[1])
 def act(A,position,vector):
  return rotate(position),(add(mul(A[0],vector[0]),mul(A[1],vector[1])),
                           add(mul(A[2],vector[0]),mul(A[3],vector[1])))
 vec=(g(2,1),g(3,-2))
 for xyz in product((-2,-1,0,1,2),repeat=3):
  p,v=xyz,vec
  for _ in range(3):p,v=act(V,p,v)
  assert (p,v)==(xyz,vec)
  p,v=xyz,vec
  for _ in range(3):p,v=act(U,p,v)
  assert p==xyz and v==tuple(neg(c) for c in vec)
 print('PASS exact Gaussian-rational SU2 matrices: q^3=-I, (-q)^3=I')
 print('PASS all 3 Pauli basis conjugations, all 3 Dirac chain-rule coefficients')
 print('PASS 9 C3 matrix group identities, 125 3-turn state tests')
 print('PASS path-selected 3 turns produce central -I on spinors, genuine lift produces +I')
 print('NOT proven: wild complement SO3-invariant open set, analytic operator extension, geometric pi1')
if __name__=='__main__':verify()
