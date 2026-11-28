#!/usr/bin/env python3
"""BR89–91: BR37 actual warped adapted inverse, full Israel defect jump,
and BR29 contracted-Bianchi/Cotton source. No continuum promotion.
Classical Lorentz, Gauss–Codazzi, Schouten and Bianchi identities are
prior mathematics; DASHI-specific work is the exact original carrier
and allocation-indexed attachment, rank and negative controls.
"""
import argparse
from itertools import combinations,combinations_with_replacement
import sympy as s
Q=s.Rational

def br89(sample,sector):
    # BR34 owns the actual full finite warped transfer, no replacement
    # by flat/exponential proxy. BR37 proved frozen Lorentz intertwining.
    import numpy as np
    from check_hopf369_br_warped_physical_attachment import operators,row_matrices
    from check_hopf369_br_full_warped_symbol import enc,dec
    from scipy.linalg import block_diag
    cases=[(4+2j,2),(3+8j,8),(3+0j,12)]
    zt,k=cases[sample]; ell=np.sqrt(zt*zt+k*k)
    a=zt/ell; b=1j*k/ell
    B=np.array([[a,b,0,0],[b,a,0,0],[0,0,1,0],[0,0,0,1]],complex)
    B5=block_diag(B,1)
    assert np.linalg.norm(B.T@np.diag([-1,1,1,1])@B-np.diag([-1,1,1,1]),np.inf)<1e-12
    def symrep(n,M):
        keys=list(combinations_with_replacement(range(n),2))
        cols=[]
        for i,j in keys:
            p=np.zeros((n,n),complex);p[i,j]=p[j,i]=1
            pp=M@p@M.T;cols.append([pp[i,j] for i,j in keys])
        return np.array(cols).T
    if sector=='metric':
        u=symrep(5,B5); t=symrep(4,B)
        T=block_diag(t,B,t,B,1,1); r=24
        perm=[*range(24),28,*range(24,28),29]
        scale=np.array([1]*14+[1/abs(ell)]*16)
        idx=0
    else:
        u=B5;T=block_diag(1,B,B,1);r=1
        perm=list(range(10));scale=np.array([1]*5+[1/abs(ell)]*5)
        idx=1
    U=block_diag(u,u)
    ops=operators()
    rest=row_matrices(s.Matrix([ell,0,0,0]),*ops,32)
    lab=row_matrices(s.Matrix([zt,1j*k,0,0]),*ops,32)
    D0=scale[:,None]*rest[idx]
    D=scale[:,None]*lab[idx]
    E0=scale[:,None]*rest[idx+2][perm,:]
    E=scale[:,None]*lab[idx+2][perm,:]
    # Scale commutes with the representation on each row block.
    # In E metric reorder the derivative rows only.
    norm=lambda x:np.linalg.norm(x,np.inf)
    close=lambda x,y: norm(x-y)<=2e-7*max(1,norm(x),norm(y))
    assert close(D@U,T@D0)
    assert close(E[r:r+1,:]@U,E0[r:r+1,:])
    kept=[i for i in range(len(D)) if i!=r]
    assert close(E[kept,:],D[kept,:])
    # Actual replacement scalar row in rest D data coordinates.
    g0=E0[r,:]; l=np.linalg.solve(D0.T,g0)
    assert norm(l[r+1:r+4])<=2e-7*max(1,abs(l[r]))
    er=np.eye(len(D))[:,r];v=np.linalg.solve(T,er)
    d=l@v
    assert abs(d-a*l[r])<2e-7*max(1,abs(d))
    assert abs(d)>1e-10
    # For ALL right-hand sides at once: complete the omitted D row
    # in rest coordinates, solve there, then transport the unknown.
    F=np.eye(len(D),dtype=complex);F[r,:]=0
    F0=np.linalg.solve(T,F)
    lam=(er-l@F0)/d
    rhs=F0+np.outer(v,lam)
    inv=U@np.linalg.solve(D0,rhs)
    assert close(E@inv,np.eye(len(D)))
    assert close(inv@E,np.eye(len(D)))
    # Positive Hermitian pullback on endpoint traces (not Lorentz
    # bilinear energy). Its frequency dependence is explicit.
    ui=np.linalg.inv(U);G=ui.conj().T@ui
    assert np.min(np.linalg.eigvalsh(G))>0
    assert close(U.conj().T@G@U,np.eye(len(D)))
    assert norm(v)/abs(a)<=1+k/abs(zt)+1e-12
    print('PASS BR89 actual BR34 warped',sector,'sample',sample,
          'D transport, E rank-one inverse and positive adapted norm; numerical not interval acceptance')
    print('rest D inverse',norm(np.linalg.inv(D0)),'E response',abs(l[r]),'adapted E factor',norm(v)/abs(a))

def br89_algebra():
    # The exact norm loss in rest coordinates does not need a boost
    # norm multiplied twice. The omitted lab temporal datum is lifted
    # by v=B^-1 e0 and its scalar denominator is a*d0.
    a,b=s.symbols('a b',nonzero=True); d=s.symbols('d',nonzero=True)
    B=s.Matrix([[a,b],[b,a]])
    Bi=s.Matrix([[a,-b],[-b,a]])
    assert B*Bi==(a*a-b*b)*s.eye(2)
    v=Bi[:,0]
    h=s.Matrix([[d,0]])
    assert (h*v)[0]==a*d
    y=s.Matrix(s.symbols('y0:2'));f=s.Symbol('f')
    lam=(f-(h*y)[0])/(a*d)
    assert s.cancel((h*(y+v*lam))[0]-f)==0
    # At z=(s,i k,0,0), |v|_infty/|a|=max(1,k/|s|).
    # Fixed positive damping suffices, but k/|s| cannot be bounded
    # uniformly as spatial frequency grows. This is an adapted norm
    # and is NOT the BR87 physical coordinate norm.
    z,k,ell=s.symbols('z k ell',nonzero=True)
    assert (v/a).subs({a:z/ell,b:s.I*k/ell})==s.Matrix([1,-s.I*k/z])
    print('PASS BR89 exact E omitted-row completion and adapted frequency factor')

def geom():
    from check_hopf369_br_curvature_energy import carrier,P,eta,read
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier()
    An=A[3];P0=s.eye(35)-An*(5*An-4*An**3)
    assert P0.rank()==9
    return C,V,X,G,Y,J,An,P0,P,eta,read
def wedge(g,M,a,b,c,d):
    return g[a,c]*M[b,d]+M[a,c]*g[b,d]-g[a,d]*M[b,c]-M[a,d]*g[b,c]
def br90():
    C,V,X,G,Y,J,An,P0,P,eta,read=geom()
    h=s.diag(*eta[:4]);g=s.diag(*eta)
    q=list(combinations_with_replacement(range(10),2))
    keys=list(combinations_with_replacement(range(4),2))
    ds=s.symbols('d:10');ms=s.symbols('m:10')
    D=s.Matrix(4,4,lambda a,b:ds[keys.index(tuple(sorted((a,b))))])
    M=s.Matrix(4,4,lambda a,b:ms[keys.index(tuple(sorted((a,b))))])
    j=Q(-6,5);t=s.trace(h*M);d=s.trace(h*D)
    # Matched h and [K]=j h, constant j:
    # Gauss scalar: [D_nn]=tr_h[D_ab]+6j tr_h M.
    # Codazzi: [D_na]=0. D is the same Ricci defect, not a fresh
    # freely discarded residual. M=(K+ + K-)/2 may have nonzero trace.
    DD=s.diag(D,d+6*j*t)
    Sch=(DD-g*s.trace(g*DD)/8)/3
    def r(a,b,c,d):
        if 4 not in (a,b,c,d):return -j*wedge(h,M,a,b,c,d)
        if (4 in (a,b))!=(4 in (c,d)):return s.S.Zero
        return (D+j*(2*M+t*h))[a,c]
    RR=s.Matrix(10,10,lambda i,k:r(*P[i],*P[k]))
    ric=s.Matrix(5,5,lambda b,d:sum(eta[a]*read(RR,a,b,a,d) for a in range(5)))
    assert (ric-DD).applyfunc(s.expand)==s.zeros(5)
    raw=s.Matrix([r(*P[a],*P[b])-wedge(g,Sch,*P[a],*P[b]) for a,b in q])
    assert (C*raw).applyfunc(s.expand)==s.zeros(C.rows,1)
    # Full BR29 jump carrier for tracefree mean; the pure trace mean
    # cancels in Weyl after the Hamiltonian jump is paid.
    Jfull=raw.jacobian(ms)
    tracefree= s.Matrix(list(M)).jacobian(ms).gauss_jordan_solve(Y)[0]
    assert Jfull*tracefree==j*V*J
    assert Jfull*s.Matrix([h[a,b] for a,b in keys])==s.zeros(55,1)
    T=V.gauss_jordan_solve(raw.jacobian(ds))[0]
    assert T.rank()==9 and (P0*T).rank()==6 and (An*T).rank()==8
    ker=s.Matrix.hstack(*((P0*T).nullspace()))
    expected=s.Matrix.hstack(s.eye(10)[:,1],s.eye(10)[:,2],s.eye(10)[:,3],s.Matrix([h[a,b] for a,b in keys]))
    assert ker.rank()==4 and ker.row_join(expected).rank()==4
    assert (P0*T)*expected==s.zeros(35,4)
    print('PASS BR90 exact curved Gauss/Codazzi/Ricci reconstruction, Weyl jump rank 9, zero-speed rank 6; kernel mixed-time plus pure trace')
    print('BR90 REFUSAL: Israel-compatible Ricci defect is not automatically in the BR29 zero-speed kernel')

def br91():
    C,V,X,G,Y,J,An,P0,P,eta,read=geom()
    g=s.diag(*eta);keys=list(combinations_with_replacement(range(5),2))
    ds=s.symbols('d1:76')
    jets=[s.Matrix(5,5,lambda a,b:ds[k*15+keys.index(tuple(sorted((a,b))))]) for k in range(5)]
    # At an orthonormal point the entries are COVARIANT first jets of
    # D=Ric+4g; contracted Bianchi is div D=1/2 d tr D.
    cb=s.Matrix([sum(eta[a]*jets[a][a,b] for a in range(5))-s.trace(g*jets[b])/2 for b in range(5)])
    cbm=cb.jacobian(ds);N=s.Matrix.hstack(*cbm.nullspace())
    assert cbm.rank()==5 and N.shape==(75,70)
    Ps=[(D-g*s.trace(g*D)/8)/3 for D in jets]
    def dw(k,a,b,c,d):return wedge(g,Ps[k],a,b,c,d)
    # Actual Weyl divergence (electric source) and differential
    # Bianchi (magnetic source) from R=W+g wedge Schouten.
    def f(a,b,c,d):
        if a==0:return -2*(Ps[c][b,d]-Ps[d][b,c])
        return -dw(0,a,b,c,d)-dw(a,b,0,c,d)-dw(b,0,a,c,d)
    raw=s.Matrix([f(*p,*q) for p in P for q in P])
    F=G.inv()*X.T*raw.jacobian(ds)
    assert (F*N).rank()==25 and (P0*F*N).rank()==9
    # Stronger negative control: D=S(C) for an actual symmetric
    # second jet of the 5-component gauge covector in flat principal
    # normal coordinates. Enforce its five wave equations exactly.
    cs=s.symbols('c:75')
    hc=lambda i,j,k:cs[k*15+keys.index(tuple(sorted((i,j))))]
    Dg=s.Matrix([(hc(k,a,b)+hc(k,b,a))/2 for k in range(5) for a,b in keys])
    Jg=Dg.jacobian(cs)
    box=s.Matrix([sum(eta[i]*hc(i,i,k) for i in range(5)) for k in range(5)]).jacobian(cs)
    assert cbm*Jg==box/2
    Ng=s.Matrix.hstack(*box.nullspace())
    assert (F*Jg*Ng).rank()==25 and (P0*F*Jg*Ng).rank()==9
    print('PASS BR91 complete BR29 Cotton source rank 25, zero-speed rank 9, even on homogeneous principal gauge wave jets')
    print('BR91 REFUSAL: algebraic projected Cotton cancellation cannot replace same-metric zero-data gauge uniqueness')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['algebra','warp','jump','cotton'],required=True)
    p.add_argument('--sample',type=int,choices=range(3),default=0)
    p.add_argument('--sector',choices=['metric','gauge'],default='metric')
    a=p.parse_args()
    if a.part=='warp':br89(a.sample,a.sector)
    else:{'algebra':br89_algebra,'jump':br90,'cotton':br91}[a.part]()
