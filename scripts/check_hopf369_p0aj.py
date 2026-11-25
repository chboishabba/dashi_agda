"""P0AJ: periodic KK Hamiltonian source, exact identities and finite-grid assay.
Localized selected density, not an evolved tension brane or continuum proof.
"""
import sympy as s
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import cg


def exact():
    p,rho,k,L=s.symbols('p rho k L',positive=True)
    jump=-k*rho*p**2/3
    assert s.simplify(-6*jump/p**3-2*k*rho/p)==0
    a=s.Matrix(s.symbols('a:3',real=True)); H=s.eye(3)+a*a.T
    g=H.row_join(a).col_join(a.T.row_join(s.ones(1,1)))
    inv=s.eye(3).row_join(-a).col_join((-a.T).row_join(s.Matrix([[1+a.dot(a)]])))
    assert (g*inv-s.eye(4)).applyfunc(s.expand)==s.zeros(4)
    assert s.expand(g.det())==1
    # Zero-mode constant source forces a quadratic spherical mean.
    r,c=s.symbols('r c',positive=True); u=1-c*r*r/6
    assert s.simplify(-s.diff(r*r*s.diff(u,r),r)/r**2-c)==0
    # Exact periodic flat massive Green normalization and jump, 0<w<L.
    m,w=s.symbols('m w',positive=True)
    G=s.cosh(m*(w-L/2))/(2*m*s.sinh(m*L/2))
    assert s.simplify(s.diff(G,w,2)-m*m*G)==0
    assert s.simplify(G.subs(w,0)-G.subs(w,L))==0
    assert s.simplify(s.diff(G,w).subs(w,0)-s.diff(G,w).subs(w,L)+1)==0
    print('PASS conformal delta scaling, KK inverse/determinant, zero-mode obstruction, periodic Green jump',flush=True)


def A(x):
    X,Y,Z=x.T; d=1+X*X+Y*Y+Z*Z
    return 2*np.stack((2*X*Z-2*Y,2*X+2*Y*Z,1-X*X-Y*Y+Z*Z),axis=1)/d[:,None]**2


def assay(N,M,eps=.25,kaprho=.1,R=1.,box=4.):
    # Cube Dirichlet comparison at fixed outer radius; Fourier circle exact periodicity.
    L=2*np.pi; h=2*box/(N+1); t=np.linspace(-box,box,N+2)[1:-1]
    X=np.stack(np.meshgrid(t,t,t,indexing='ij'),axis=-1).reshape(-1,3); n=len(X)
    r2=np.sum(X*X,axis=1); V=eps**2*64/(12*(1+r2)**4); av=eps*A(X)
    dens=kaprho*np.maximum(1-r2/R**2,0)**2*np.sqrt(1+np.sum(av*av,axis=1))/(3*L)
    ix=np.arange(n).reshape(N,N,N); links=[]
    for j in range(3):
        lo=[slice(None)]*3; hi=lo.copy();lo[j]=slice(None,-1);hi[j]=slice(1,None)
        i=ix[tuple(lo)].ravel(); l=ix[tuple(hi)].ravel(); phase=eps*h*A((X[i]+X[l])/2)[:,j];links.append((i,l,phase))
    matrices=[]
    for mode in range(M+1):
        rows=[np.arange(n)];cols=[np.arange(n)];vals=[6/h**2+mode**2-V]
        for i,j,p in links:
            u=-np.exp(-1j*mode*p)/h**2;rows.extend([i,j]);cols.extend([j,i]);vals.extend([u,u.conj()])
        matrices.append(coo_matrix((np.concatenate(vals),(np.concatenate(rows),np.concatenate(cols))),shape=(n,n)).tocsr())
    U=np.zeros((M+1,n),complex); trace=np.ones(n); maxres=0.
    for step in range(30):
        old=trace.copy(); src=dens*old**2
        for m,B in enumerate(matrices):
            rhs=src+(V if m==0 else 0); sol,info=cg(B,rhs,x0=U[m],rtol=2e-11,atol=1e-13,maxiter=1000)
            assert info==0;U[m]=sol;maxres=max(maxres,np.max(np.abs(B@sol-rhs)))
        trace=1+U[0].real+2*U[1:].real.sum(axis=0)
        if np.max(abs(trace-old))<1e-11:break
    else:raise AssertionError('fixed point')
    sample=np.array([1+U[0].real+2*np.real(np.exp(1j*np.arange(1,M+1)*w)@U[1:]) for w in np.linspace(0,2*np.pi,17)])
    q=8*eps**2/9; alpha=kaprho*np.sqrt(1+4*eps**2)*(R**2/2+2*R)/(3*L); bound=2/(1-q)
    assert alpha<(1-q)**2/4 and maxres<1e-8 and sample.min()>0 and sample.max()<bound
    assert np.linalg.norm(U[1])>0 and np.max(abs(U[0].imag))<1e-10
    i=np.argmin(r2); defect=max(np.max(abs(B@U[m]-(dens*trace**2+(V if m==0 else 0)))) for m,B in enumerate(matrices))
    print(dict(N=N,M=M,iterations=step+1,center_trace=trace[i],center_zero=1+U[0,i].real,center_nonzero=trace[i]-1-U[0,i].real,mode1_norm=np.linalg.norm(U[1]),maxres=maxres,defect=defect,min=float(sample.min()),max=float(sample.max()),q=q,alpha=alpha,analytic_bound=bound),flush=True)


if __name__=='__main__':
    exact()
    for N,M in [(11,4),(11,8),(15,8),(15,12)]:assay(N,M)
