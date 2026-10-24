#!/usr/bin/env python3
"""SU(3) infinite-image horned commutator tower: constructive numerical audit.

Original roots:
  Morikuni Gotô, "A Theorem on compact semi-simple groups", JMSJ 1
  (1949), 270–272, DOI 10.2969/jmsj/00130270.
  Hatcher, Algebraic Topology, Example 2B.2, commutator-stage tower.
  J. W. Alexander (1924), original horned sphere.

Repo owners:
  DASHI/Mathematics/Topology/AlexanderHornedC3CompactCommutatorRepresentationExact.agda
  Sibling PR #1247: selected nonzero-CP U, T*S1, Q(zeta3) invariants.

New DASHI calculation:
  For a chosen A in SU(3), diagonalize A=V diag(lambda) V^dagger.
  Let P cyclically shift basis vectors e_j -> e_{j+1}; det P=+1.
  Set d=(1,1/lambda[1],lambda[0]), scale d by common phase to det D=1.
  Then [P,D]=diag(lambda). Therefore
       X=V P V^dagger, Y=V D V^dagger, [X,Y]=A.
  Recursively choose [X_w,Y_w]=A_w on all binary horns. For sector i,
  rho_i(g)=T^i rho_0(g) T^{-i}, so rotation maps to conjugation by T.

This is a finite numerical floating-point regression, NOT an Agda kernel
certificate of the infinite colimit, source topology, or physical QFT.
No claim that the generated image is dense in SU(3); only the root
is independently known to have infinite order by a Galois-trace theorem.
"""

from math import pi
import numpy as np
from scipy.linalg import schur

I3=np.eye(3,dtype=complex)
P=np.array([[0,0,1],[1,0,0],[0,1,0]],dtype=complex)
ZETA=np.exp(2j*pi/3)
S12,C12=161/289,240/289
S13,C13=240/1609,1591/1609
S23,C23=20/29,21/29

def target_matrix():
    U=np.array([
        [C12*C13,S12*C13,S13*ZETA.conjugate()],
        [-S12*C23-C12*S23*S13*ZETA,
          C12*C23-S12*S23*S13*ZETA,S23*C13],
        [S12*S23-C12*C23*S13*ZETA,
          -C12*S23-S12*C23*S13*ZETA,C23*C13]
    ],dtype=complex)
    T=np.diag([1,ZETA,ZETA*ZETA])
    S=U@np.diag([1,-1,-1])@U.conj().T
    return T,S,T@S

def commutator(A,B):
    return A@B@A.conj().T@B.conj().T

def factor_su3(A):
    # Schur decomposition, with diagonal triangular Schur form for
    # the normal/unitary A. Handles repeated eigenvalues.
    H,V=schur(A,output="complex")
    assert np.linalg.norm(H-np.diag(np.diag(H)))<1e-10
    lam=np.diag(H)
    d=np.array([1,1/lam[1],lam[0]],dtype=complex)
    d=d/(np.prod(d)**(1/3))
    X=V@P@V.conj().T
    Y=V@np.diag(d)@V.conj().T
    return X,Y

def run(depth=5,tolerance=1e-10):
    T,S,A=target_matrix()
    assert np.linalg.norm(np.linalg.matrix_power(T,3)-I3)<tolerance
    assert np.linalg.norm(A@A.conj().T-I3)<tolerance
    assert abs(np.linalg.det(A)-1)<tolerance
    assert np.linalg.norm(np.linalg.matrix_power(A,5)-I3)>1e-2

    nodes={():A}
    max_error=max_det=max_unitarity=0.0
    count=0
    root_children=None
    for level in range(depth):
        nxt={}
        for w,g in nodes.items():
            x,y=factor_su3(g)
            if level==0: root_children=(x,y)
            error=np.linalg.norm(commutator(x,y)-g)
            max_error=max(max_error,error)
            count+=1
            for z in (x,y):
                max_unitarity=max(max_unitarity,np.linalg.norm(z@z.conj().T-I3))
                max_det=max(max_det,abs(np.linalg.det(z)-1))
            nxt[w+(0,)]=x
            nxt[w+(1,)]=y
        nodes=nxt
    assert count==(2**depth-1)
    assert max_error<tolerance and max_det<tolerance and max_unitarity<tolerance

    x,y=root_children
    max_equivariance=0.0
    for sector in range(3):
        Q=np.linalg.matrix_power(T,sector)
        f=lambda g:Q@g@Q.conj().T
        max_equivariance=max(max_equivariance,
            np.linalg.norm(commutator(f(x),f(y))-f(A)))
    assert max_equivariance<tolerance

    print(f"horn root in SU3; root order: infinite by external exact Galois trace")
    print(f"binary refinements: {depth} levels; {count} parents / {2**depth} leaves")
    print(f"commutator error: {max_error:.3g}")
    print(f"unitarity defect: {max_unitarity:.3g}; det defect: {max_det:.3g}")
    print(f"threefold twist-equivariance defect: {max_equivariance:.3g}")
    print(f"||A^5-I||: {np.linalg.norm(np.linalg.matrix_power(A,5)-I3):.12g}")
    print("abstract infinite-image model candidate: NUMERICALLY CONSTRUCTED")
    print("geometric pi1, Agda/Lean kernels, PMNS physics, density: NOT ESTABLISHED")
    return dict(depth=depth,parent_count=count,
        max_commutator_error=max_error,max_unitarity=max_unitarity,
        max_det=max_det,max_twist=max_equivariance)

if __name__=="__main__":
    run()
