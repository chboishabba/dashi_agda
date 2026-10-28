#!/usr/bin/env python3
"""C3 spin fixed-axis selection, orbit Fourier projector, mod-3 collision.

Reuses exact Gaussian-rational SU(2) matrix from the existing Dirac audit.
No geometry, spectra, p-adic analytic field or Monster module asserted.
"""
from fractions import Fraction as F
from itertools import product
from alexander_horned_c3_spin_dirac_probe import (
    g, add, neg, mul, scale, mm, madd, mscale, mpow,
    ZERO, ONE, MID, V,
)

def sub(a,b):return add(a,neg(b))
def det2(A):return sub(mul(A[0],A[3]),mul(A[1],A[2]))
def trace2(A):return add(A[0],A[3])

def matrix_zero(n):return tuple(tuple(ZERO for _ in range(n)) for _ in range(n))
def matrix_id(n):return tuple(tuple(ONE if i==j else ZERO for j in range(n)) for i in range(n))
def matrix_add(A,B):return tuple(tuple(add(x,y) for x,y in zip(a,b)) for a,b in zip(A,B))
def matrix_scale(s,A):return tuple(tuple(scale(s,x) for x in row) for row in A)
def matrix_mul(A,B):
    n=len(A)
    return tuple(tuple(sum_gauss(mul(A[i][k],B[k][j]) for k in range(n)) for j in range(n)) for i in range(n))
def sum_gauss(v):
    out=ZERO
    for item in v:out=add(out,item)
    return out

def check():
    assert trace2(V)==g(-1) and det2(V)==ONE
    assert det2(tuple(sub(a,b) for a,b in zip(V,MID)))==g(3)
    # A fixed spatial point x=(t,t,t) carries a 2-spinor fibre;
    # no nonzero C3 invariant spinor exists in characteristic zero.
    assert det2(tuple(sub(a,b) for a,b in zip(V,MID))) != ZERO
    # Orbit of THREE different spatial points, each with two spinor
    # components. The proper spin action shifts points and acts by V.
    T=[[ZERO for _ in range(6)] for _ in range(6)]
    for k,a,b in product(range(3),range(2),range(2)):
        T[2*((k+1)%3)+a][2*k+b]=V[2*a+b]
    T=tuple(tuple(row) for row in T)
    I6=matrix_id(6)
    T2=matrix_mul(T,T)
    assert matrix_mul(T2,T)==I6
    P0=matrix_scale(F(1,3),matrix_add(I6,matrix_add(T,T2)))
    assert matrix_mul(P0,P0)==P0
    assert matrix_mul(T,P0)==P0 and matrix_mul(P0,T)==P0
    assert sum_gauss(P0[i][i] for i in range(6))==g(2)
    # Q_3 has no primitive cube root: the rational 2-dimensional
    # cyclotomic representation has companion matrix C.
    A=((0,-1),(1,-1))
    def mm3(X,Y):return tuple(tuple(sum(X[i][k]*Y[k][j] for k in range(2))%3 for j in range(2)) for i in range(2))
    B=tuple(tuple(v%3 for v in row) for row in A)
    assert mm3(mm3(B,B),B)==((1,0),(0,1))
    invs=[]
    for a,b in product(range(3),repeat=2):
        if ((B[0][0]*a+B[0][1]*b)%3, (B[1][0]*a+B[1][1]*b)%3)==(a,b):invs.append((a,b))
    assert len(invs)==3   # line of F3-fixed vectors, dimension 1
    # Char poly X²+X+1 becomes (X-1)² mod 3: new modular fixed vectors
    # without rational/3-adic fixed vectors; Maschke failure.
    assert ((-1)%3, 1) == (2,1)
    print('PASS axial spinor: trace(S)=-1, det(S)=1, det(S-I)=3, fixed dimension 0')
    print('PASS free 3-point orbit x 2-spinor: T³=I, P0²=P0, invariant rank 2')
    print('PASS mod-3 cyclotomic companion C³=I, 1D fixed space appears in F3')
    print('NOT proven: geometric horn axis, full Dirac spectral domain, 3B same-object map')

if __name__=='__main__':check()
