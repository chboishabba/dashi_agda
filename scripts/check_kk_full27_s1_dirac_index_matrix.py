#!/usr/bin/env python3
"""Full 27 finite cyclic Dirac-index control for smooth 5D S1.

For a square matrix-valued, smooth periodic 5D bulk mass M(y) the
continuum first-order operator d/dy+M(y) on a closed circle has
Fredholm index zero (homotopy to d/dy). This independent finite test
ONLY proves the selected finite cyclic analogue by exact rank-nullity.
It is NOT a kernel formalisation of the continuum index theorem.
Does not apply to orbifold/asymmetric boundary domains, defects,
higher dimensional flux or chiral brane-localised matter.
Original orbifold anomaly sources Arkani-Hamed/Cohen/Georgi 2001,
Scrucca/Serone/Silvestrini/Zwirner 2002. Current repo prior:
KKCircleQEDChiralityConsumerExact and #1106 full27 branching.
"""
import sympy as s
N=5; rank=27
T=s.zeros(N)
for i in range(N): T[(i+1)%N,i]=1
D=s.kronecker_product(T-s.eye(N),s.eye(rank))
assert D.rows==135
assert D.rank()==135-rank
assert D.H.rank()==D.rank()
assert len(D.nullspace())==len(D.H.nullspace())==rank

# Mass matrices on different sites do NOT commute. Exact 6x6 example.
sites=3; d=2
C=s.zeros(sites)
for i in range(sites):C[(i+1)%sites,i]=1
B=s.Matrix(s.kronecker_product(C-s.eye(sites),s.eye(d)))
blocks=[s.Matrix([[0,1],[2,0]]),
        s.Matrix([[1,2],[0,3]]),
        s.Matrix([[1,0],[1,2]])]
assert blocks[0]*blocks[1]!=blocks[1]*blocks[0]
for site,M in enumerate(blocks):
    for i in range(d):
        for j in range(d):B[site*d+i,site*d+j]+=M[i,j]
assert B.rank()==B.H.rank()
assert B.rows-B.rank()==B.cols-B.H.rank()
print("PASS exact 27-representation smooth cyclic analogue: 27 left and 27 right zero modes")
print("PASS finite noncommuting matrix mass example: nullity(D)=nullity(D-adjoint)")
print("LIMIT finite index fixture supports, but does not prove, continuum Fredholm homotopy index=0")
