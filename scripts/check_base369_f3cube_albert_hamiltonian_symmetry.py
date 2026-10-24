#!/usr/bin/env python3
"""Exact F3^3 vs cyclic-27 / open-cube Hamiltonian regression.
Griess 1990 J.Algebra 131: A=3^3 : SL(3,3) on Albert 27 chars.
This is a combinatorial/Hilbert lattice model, NOT actual Albert
multiplication nor the distinct Monster Griess VOA representation.
See / user-delivered check_369_albert_f3cube_hamiltonian.py for
the full local 5616-element group enumeration.
"""
from collections import Counter
from itertools import product
import sympy as s
P=list(product(range(3),repeat=3));ix={p:i for i,p in enumerate(P)}
I=s.eye(27);J=s.ones(27,27);P0=J/27;Q=I-P0
assert P0*P0==P0 and Q*Q==Q and P0*Q==s.zeros(27)
assert s.trace(P0)==1 and s.trace(Q)==26
def lap(wrap):
 L=s.zeros(27);E=set()
 for p in P:
  for a in range(3):
   if wrap or p[a]<2:
    v=list(p);v[a]=(v[a]+1)%3;q=tuple(v)
    E.add(tuple(sorted((p,q))))
 for p,q in E:
  i,j=ix[p],ix[q];L[i,i]+=1;L[j,j]+=1;L[i,j]-=1;L[j,i]-=1
 return L,E
A,E=lap(False);B,F=lap(True)
assert len(E)==54 and len(F)==81 and E<F
assert A*P0==s.zeros(27) and B*P0==s.zeros(27)
assert Counter(A.eigenvals())==Counter({0:1,1:3,2:3,3:4,4:6,5:3,6:3,7:3,9:1})
assert Counter(B.eigenvals())==Counter({0:1,3:6,6:12,9:8})
delta=s.zeros(27,1);delta[ix[(0,0,0)]]=1
assert P0*delta==s.ones(27,1)/27 and P0*delta!=delta
# SL3 shear (x,y,z)->(x+y,y,z); preserves 1+26, but not
# either native path or periodic-torus nearest-neighbour coupling.
S=s.zeros(27)
for p in P:S[ix[((p[0]+p[1])%3,p[1],p[2])],ix[p]]=1
assert S.T*S==I and S*Q==Q*S
assert A*S!=S*A and B*S!=S*B
# Affine A:SL3 forces pair-transitivity and hence H=gamma*Q.
H=27*Q
assert H*S==S*H
assert all(H[i,j]==(26 if i==j else -1) for i in range(27) for j in range(27))
assert dict(H.eigenvals())=={s.Integer(0):1,s.Integer(27):26}
assert len({(i,j) for i in range(27) for j in range(i+1,27) if H[i,j]!=0})==351
print("PASS geometric/open 54, periodic F3^3 81, fully affine-invariant 351 edges")
print("PASS distinct L spectra and rank1+rank26 projector with centre != scalar identity")
print("PASS SL3 shear breaks local Hamiltonians and preserves 1+26")
print("GATE this is not Griess 1990 Albert product or a Monster 27A/B operator")
