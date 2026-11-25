"""Exact compact FV bi-Laplacian range and receiver-specific modal split.
Nodal moments are NOT piecewise-constant shell moments. Alternative source
constructors are diagnostics, not replacements of original cell integrals.
"""
import json, hashlib
from pathlib import Path
import numpy as np
import sympy as s
from scipy.linalg import eigh_tridiagonal
from ksw668_f8_fv_source_flux import exact_cell_averages


def exact():
    count=0
    for d in (3,7,11):
        for m in (1,2,5,8):
            n=m+2;h=s.Rational(1,2)
            w=[((j+h)**d-max(j-h,0)**d)/d for j in range(n)]
            f=[(j+h)**(d-1) for j in range(n)]
            A=s.Matrix(n,n,lambda i,j: ((f[i]+(f[i-1] if i else 0)) if i==j else -f[i] if j==i+1 else -f[j] if i==j+1 else 0)/w[i])
            B=A*A[:,:m];C=s.Matrix([[w[j] for j in range(n)],[w[j]*j*j for j in range(n)]])
            assert C*B==s.zeros(2,m) and B.rank()==m and C.rank()==2
            def inv(g):
                accum=s.S.Zero;flux=[]
                for j in range(n):accum+=w[j]*g[j];flux.append(accum/f[j])
                x=[s.S.Zero]*n;accum=s.S.Zero
                for j in reversed(range(n)):accum+=flux[j];x[j]=accum
                return s.Matrix(x)
            # Entire kernel, not just a chosen example.
            for g in C.nullspace():
                y=inv(g);x=inv(y)
                assert A*y==g and A*x==y and y[-1]==0 and x[-2:]==[0,0]
                assert B*x[:m,0]==g
                count+=1
            # Reject replacing shell mean of r² by node value (the two duals differ).
            shell=s.Matrix([[((j+h)**(d+2)-max(j-h,0)**(d+2))/(d+2) for j in range(n)]])
            assert shell*B!=s.zeros(1,m)
    return count


def numeric(work):
    dr=.006;eps=.04;n=502;r=np.arange(n)*dr;a=np.maximum(r-dr/2,0);b=r+dr/2;w=(b**3-a**3)/3
    p=b*b/(dr*w);m=a*a/(dr*w)
    diag=p+m;off=-np.sqrt(p[:-1]*m[1:]);lam,V=eigh_tridiagonal(diag,off)
    g=exact_cell_averages(eps,np.arange(n+1)*dr,dr)[0,:-1]
    def digest(x):return hashlib.sha256(np.ascontiguousarray(x).tobytes()).hexdigest()
    with np.load(work/'ledger-far-e4-source-vjp.npz',allow_pickle=False) as z:
        assert int(z['k'])==0
        k=z['grad'];assert digest(k)==z['grad_sha'].item()=='7a4ae45d9fc4c6cee2e884b63c8c634b68aedee70b26be9051ab540cddff9f9a'
        k=k[:-1]
    G=V.T@(np.sqrt(w)*g);K=V.T@(k/np.sqrt(w));v=G*K
    assert abs(v.sum()-k@g)<1e-13
    cuts=[]
    for cutoff in (8,16,32,64,128,256,n):
        q=v[cutoff:];bound=np.linalg.norm(G[cutoff:])*np.linalg.norm(K[cutoff:])
        assert abs(q.sum())<=bound+1e-20
        cuts.append(dict(modes=cutoff,omega_last=float(np.sqrt(lam[cutoff-1])),source_energy_fraction=float(np.sum(G[:cutoff]**2)/np.sum(G**2)),signed_low=float(v[:cutoff].sum()),signed_tail=float(q.sum()),absolute_tail=float(np.abs(q).sum()),cauchy_tail=float(bound)))
    # Optimal M-norm correction on original source cells, no receiver fitting.
    idx=np.flatnonzero(g);u=r[idx]/eps;ww=w[idx];shell=((b[idx]**5-a[idx]**5)/5/ww)/eps**2
    shell4=((b[idx]**7-a[idx]**7)/7/ww)/eps**4
    cases=[]
    for name,C in [('nodal',np.stack((np.ones_like(u),u*u))),('shell',np.stack((np.ones_like(u),shell))),('both',np.stack((np.ones_like(u),u*u,shell))),('shell_024',np.stack((np.ones_like(u),shell,shell4)))]:
        desired=np.zeros(len(C))
        if name=='shell_024':desired[-1]=eps**3*4.579857566126423
        residual=C@(ww*g[idx])-desired
        correction=C.T@np.linalg.solve((C*ww)@C.T,residual)
        gg=g.copy();gg[idx]-=correction
        assert np.max(abs(C@(ww*gg[idx])-desired))<1e-10
        cases.append(dict(name=name,relative_change=float(np.linalg.norm(np.sqrt(w)*(gg-g))/np.linalg.norm(np.sqrt(w)*g)),far_e4=float(k@gg),nodal_m2=float((ww*u*u)@gg[idx]),shell_m2=float((ww*shell)@gg[idx])))
    return dict(gradient_sha256='7a4ae45d9fc4c6cee2e884b63c8c634b68aedee70b26be9051ab540cddff9f9a',finite_response=float(k@g),modal_response=float(v.sum()),modal_absolute=float(np.abs(v).sum()),cuts=cuts,moment_corrections=cases)

if __name__=='__main__':
    import sys
    print(json.dumps(dict(exact_basis_inverse_checks=exact(),**numeric(Path(sys.argv[1]))),indent=2))
