#!/usr/bin/env python3
"""S4c: exact conductance-history compression; selected finite graph, not kinetics."""
from sympy import Matrix, eye, ones, zeros, exp, simplify, __version__
from reactive_pnp_369 import POINTS, BONDS, poisson_matrix


def check():
    B=zeros(len(POINTS),len(BONDS))
    for e,(a,b) in enumerate(BONDS):
        B[a,e],B[b,e]=-1,1
    A=B[:26,:]
    Z=Matrix.hstack(*B.nullspace())
    assert A.shape==(26,54) and Z.shape==(54,28)
    # D=diag(ratios) preserves cycle space iff ratios agree within
    # every circuit. Fundamental cycle support equalities suffice.
    eq=[]
    for z in Z.columnspace():
        support=[i for i,v in enumerate(z) if v]
        for e in support[1:]:
            eq.append(eye(54)[e,:]-eye(54)[support[0],:])
    C=Matrix.vstack(*eq)
    assert C.to_DM().rank()==53 and C*ones(54,1)==zeros(C.rows,1)
    # Fixed reference reconstruction K, reduced divergence coordinates.
    Linv=(A*A.T).inv(method='DM'); K=A.T*Linv
    assert A*K==eye(26) and Z.T*K==zeros(28,26)
    assert K == 7*A.T*(7*A*A.T).inv(method='DM')
    P=eye(54)-K*A
    assert A*P==zeros(26,54) and P*Z==Z and P*P==P
    # Single-edge rank-one weight change via Sherman-Morrison.
    # K_e-K = (P e)(e^T K)/(1+e^T K A e).
    directions=[]
    for i in range(54):
        e=eye(54)[:,i]
        a=A*e
        denom=1+(a.T*Linv*a)[0]
        correction=P*e*(e.T*K)/denom
        assert A*correction==zeros(26,26)
        assert correction.to_DM().rank()==1
        directions.append(P*e)
    assert Matrix.hstack(*directions).to_DM().rank()==28
    e=eye(54)[:,0]; W=eye(54)+e*e.T
    K2=W*A.T*(A*W*A.T).inv(method='DM')
    correction=P*e*(e.T*K)/(1+(e.T*K*A*e)[0])
    assert K2-K==correction
    d=A*e
    J1=K*d; J2=-K2*d; total=J1+J2
    assert A*total==zeros(26,1) and total!=zeros(54,1)
    # Exact streaming cycle coordinates relative to reference.
    G=(Z.T*Z).inv(method='DM')*Z.T
    assert Z*G*P==P
    assert K*(d-d)+Z*(G*P*J1+G*P*J2)==total
    # Native Poisson geometry, unit scales: integral entries checked.
    raw=poisson_matrix(1)
    assert all(float(v).is_integer() for v in raw.flat)
    L=Matrix(raw.astype(int).tolist())
    assert L==B*B.T+Matrix.diag(*(2*sum(abs(x)==1 for x in p) for p in POINTS))
    psi=eye(27)[:,0]-eye(27)[:,26]
    rho=L*psi
    assert sum(rho)==0
    plus=10*ones(27,1)+rho/2; minus=10*ones(27,1)-rho/2
    assert min(plus)>0 and min(minus)>0 and sum(plus)==sum(minus)==270
    assert L.inv(method='DM')*(plus-minus)==psi
    # Baseline charge zero -> psi=0, weights=1. Perturbed psi yields
    # weight 1/(exp(1)-1) on edges at positive corner, 1 on unaffected edges.
    a,b=BONDS[0]; assert psi[a]==1 and psi[b]==0
    w0=simplify((psi[b]-psi[a])/(exp(psi[b]-psi[a])-1)*exp(-psi[a]))
    assert simplify(w0-1/(exp(1)-1))==0 and w0!=1
    assert any(psi[a]==psi[b]==0 for a,b in BONDS)
    print(f'SymPy {__version__}: native ratio constraint rank 53; common scale only')
    print('54/54 edge perturbations rank one; union spans 28 cycle dimensions')
    print('exact streaming residual reconstruction; positive same-mass Poisson states PASS')


if __name__=='__main__':
    check()
