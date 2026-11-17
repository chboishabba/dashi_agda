#!/usr/bin/env python3
"""Faithful 6-complex-dimensional (2I)^3 rtimes C3 spin actor.

Three SU2 spin-doublet channels and a cyclic permutation. This is
laboratory-friendly finite algebra, not a measured wild-space holonomy.
Requires adjacent alexander_horned_c3_finite_SU2_gauge_simulator.py.
"""
import random
import alexander_horned_c3_finite_SU2_gauge_simulator as S
G,q,section,root=S.build()
def matrix(q):
 a,b,c,d=S.tofloat(q)
 return ((complex(a,b),complex(c,d)),
         (complex(-c,d),complex(a,-b)))
def matmul(A,B):
 return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(len(B)))
    for j in range(len(B[0]))) for i in range(len(A)))
def mv(A,v):return tuple(sum(x*y for x,y in zip(row,v)) for row in A)
def act(actor,v):
 x,k=actor
 return tuple(mv(matrix(x[j]),v[(j-k)%3]) for j in range(3))
def product_actor(a,b):
 x,k=a;y,l=b
 return tuple(S.mul(x[j],y[(j-k)%3]) for j in range(3)),(k+l)%3
def check():
 eye=((1+0j,0j),(0j,1+0j))
 for q in G:
  M=matrix(q)
  adj=tuple(tuple(x.conjugate() for x in row) for row in zip(*M))
  U=matmul(M,adj)
  assert all(abs(U[i][j]-eye[i][j])<1e-12 for i in range(2) for j in range(2))
  assert abs(M[0][0]*M[1][1]-M[0][1]*M[1][0]-1)<1e-12
 rng=random.Random(25)
 for _ in range(300):
  x=rng.choice(G);y=rng.choice(G)
  P=matrix(S.mul(x,y));Q=matmul(matrix(x),matrix(y))
  assert all(abs(P[i][j]-Q[i][j])<1e-12 for i in range(2) for j in range(2))
 ident=(S.ID,S.ID,S.ID)
 actors=[(ident,k) for k in range(3)]
 actors.extend((tuple(rng.choice(G) for _ in range(3)),rng.randrange(3))
               for _ in range(40))
 for a in actors:
  for b in actors[::3]:
   ab=product_actor(a,b)
   v=tuple((complex(rng.random()),complex(rng.random())) for _ in range(3))
   L=act(ab,v);R=act(a,act(b,v))
   assert all(abs(L[j][t]-R[j][t])<2e-12 for j in range(3) for t in range(2))
 m=((q,S.ID,S.ID),0)
 m3=product_actor(product_actor(m,m),m)
 assert m3==((S.NEG,S.ID,S.ID),0)
 v=((1+0j,0j),(1+0j,0j),(1+0j,0j))
 assert act(m3,v)==((-1+0j,0j),(1+0j,0j),(1+0j,0j))
 print('PASS 120 unitary SU2 matrices and 300 product checks')
 print('PASS complete C3 semidirect block action in 6 complex dimensions')
 print('PASS root cube diag(-I2,I2,I2); projective A5 erases the sign')
 print('NOTE: synthetic algebra, not a wild-space physical experiment')
if __name__=='__main__':check()
