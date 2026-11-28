"""Exact rectangular cochain ADE harmonic/reverse weld.
Same endpoint mass maps; finite temporal response, not measured scattering.
"""
import sympy as S
from solar_gauss_ade_weld import augmented_step

def periodic(maps,source):
    n=maps[0][0].rows;M=S.eye(n);b=S.zeros(n,1)
    for (T,F),u in zip(maps,source):M=T*M;b=T*b+F*u
    L=S.eye(n)-M
    # Invariant sectors need an explicitly compatible initial chart.
    if L.rank()!=L.row_join(b).rank():raise ValueError('incompatible periodic forcing')
    x,params=L.gauss_jordan_solve(b);x=x.subs({p:0 for p in params})
    states=[x]
    for (T,F),u in zip(maps,source):states.append(T*states[-1]+F*u)
    assert states[-1]==x
    return states,M,L.nullspace()

def reverse_ports(maps,observations,initial,target):
    """Finite-time affine reachability; return exact residual and null fibre."""
    n=initial.rows;M=S.eye(n);R=S.zeros(n,0)
    for T,F in maps:M=T*M;R=(T*R).row_join(F)
    O=S.Matrix(observations);A=O*R;b=target-O*M*initial
    # orthogonal range decomposition over rationals, no invented control
    basis=A.columnspace()
    B=S.Matrix.hstack(*basis) if basis else S.zeros(A.rows,0)
    P=B*(B.T*B).inv()*B.T if basis else S.zeros(A.rows)
    admitted=P*b;residual=b-admitted
    u,params=A.gauss_jordan_solve(admitted);u=u.subs({p:0 for p in params})
    assert A*u+residual==b and A.T*residual==S.zeros(A.cols,1)
    return dict(control=u,residual=residual,null_fibre=A.nullspace(),reachable=residual==S.zeros(b.rows,1),physical_admission=False)

def harmonic_columns(maps,lam,root):
    """Rectangular N-phase transfer; explicit singular compatibility guard."""
    N=len(maps);n,p=maps[0][1].shape
    if not N or lam==0 or S.simplify(root**N-1)!=0 or any(S.simplify(root**k-1)==0 for k in range(1,N)):raise ValueError('primitive root')
    H=S.zeros(N*n,N*p)
    for j in range(N):
        for k in range(p):
            M=S.eye(n);b=S.zeros(n,1);u=S.eye(p)[:,k]
            for t,(T,F) in enumerate(maps):M=T*M;b=T*b+F*u*(lam*root**j)**t
            L=lam**N*S.eye(n)-M
            if L.det()==0:raise ValueError('singular harmonic chart; restrict invariant sector explicitly')
            z=L.inv()*b;states=[z]
            for t,(T,F) in enumerate(maps):z=T*z+F*u*(lam*root**j)**t;states.append(z)
            for m in range(N):
                H[m*n:(m+1)*n,j*p+k]=sum((states[t]*root**(-m*t)/lam**t for t in range(N)),S.zeros(n,1)).applyfunc(S.simplify)/N
    return H
