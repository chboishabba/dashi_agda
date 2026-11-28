"""Reduced history return for the actual delayed mediator.
Only ratios are read from history; flight energy is a dependent ledger.
Finite piecewise-linear history sections, not interval spectral certificates.
"""
import numpy as np
from scipy.integrate import solve_ivp, quad_vec
from scipy.linalg import eigvals
from solar_steelman_delayed_tangent import construct

def reduced(m,a,delay=.01,gain=100.):
    full,_,orbit=construct(m,a,delay,gain)
    n=len(a['models']);d=len(orbit(0))-2*(n-1);nc=d-5*n-4
    edges=[(a['parent'][j],j,float(a['flows'][j])) for j in a['order'][1:]]
    coeff=[{k:complex(v) for k,v in c.items()} for _,_,c in a['models']]
    def R(t):
        u=np.exp(1j*t)
        s=np.array([sum(v*u**k for k,v in c.items()).real for c in coeff])
        sp=np.array([sum(1j*k*v*u**k for k,v in c.items()).real for c in coeff])
        V=np.zeros((n,d));j=np.arange(n)
        V[j,nc+j]=V[j,nc+n+j]=1/s
        V[j,nc+2*n+j]=sp/s;V[j,nc+3*n+j]=-sp/s
        return V
    def matrices(t):
        A,B,C=full(t)
        B1=np.zeros((d,n));B2=np.zeros((d,n))
        def add(M,cell,src,c):
            M[nc+cell,src]+=c/2;M[nc+n+cell,src]+=c/2
        for k,l,f in edges:
            src,dst,F=(k,l,f) if f>0 else (l,k,-f)
            add(B1,src,dst,-(F-gain))
            add(B1,dst,src,F+gain)
            add(B2,dst,dst,F-gain)
        return A[:d,:d],B1,B2
    def verify():
        for t in np.linspace(0,2*np.pi,5):
            A,B,C=full(t);D,U,V=matrices(t)
            assert np.allclose(D,A[:d,:d])
            assert np.allclose(U@R(t-delay),B[:d,:d])
            assert np.allclose(V@R(t-2*delay),C[:d,:d])
            assert all(np.count_nonzero(X[:d,d:])==0 for X in (A,B,C))
        print('PASS exact structural delay factorization (numerical readback)',d,n,flush=True)
    return matrices,R,d,n,verify

def block(m,a,delay,knots,start,stop,tol,out):
    mat,R,d,n,verify=reduced(m,a,delay);verify()
    if knots<2:raise ValueError('at least two history intervals')
    # Current state plus ratio history at knots excluding t=0; endpoint
    # ratio determined by current state, not an independent variable.
    grid=np.linspace(-2*delay,0,knots+1);size=d+n*knots
    if not 0<=start<stop<=size:raise ValueError('invalid block')
    k=stop-start
    basis=np.eye(size)[:,start:stop];Y=basis[:d].copy()
    past=np.concatenate((basis[d:].reshape(knots,n,k),(R(0)@Y)[None]),axis=0)
    pieces=[]
    def hist(s):
        if s<=0:
            j=min(knots-1,max(0,np.searchsorted(grid,s,side='right')-1))
            alpha=(s-grid[j])/(grid[j+1]-grid[j])
            return (1-alpha)*past[j]+alpha*past[j+1]
        for lo,hi,sol in reversed(pieces):
            if lo-1e-12<=s<=hi+1e-12:return R(s)@sol(min(hi,max(lo,s))).reshape(d,k)
        raise RuntimeError('history gap')
    def f(t,y):
        A,B,C=mat(t)
        return (A@y.reshape(d,k)+B@hist(t-delay)+C@hist(t-2*delay)).ravel()
    t=0.;T=2*np.pi
    while t<T-1e-12:
        end=min(T,t+delay)
        s=solve_ivp(f,(t,end),Y.ravel(),method='DOP853',rtol=tol,atol=tol*.01,dense_output=True)
        if not s.success:raise RuntimeError(s.message)
        pieces.append((t,end,s.sol));Y=s.y[:,-1].reshape(d,k);t=end
        # Only last two delays needed; retain enough for endpoint history.
        pieces=[p for p in pieces if p[1]>=t-2*delay-1e-12]
    M=np.vstack((Y,*[hist(T+s) for s in grid[:-1]]))
    assert M.shape==(size,k) and np.isfinite(M).all()
    np.savez(out,M=M,start=start,stop=stop,delay=delay,knots=knots,tol=tol)
    print('PASS finite history return block',size,start,stop,flush=True)

def assemble(paths):
    chunks=[]
    for path in paths:
        with np.load(path,allow_pickle=False) as f:
            chunks.append((int(f['start']),int(f['stop']),float(f['delay']),int(f['knots']),float(f['tol']),f['M']))
    chunks.sort(key=lambda c:c[0]);cursor=0;size=chunks[0][-1].shape[0]
    for lo,hi,delay,knots,tol,M in chunks:
        assert lo==cursor and (delay,knots,tol)==chunks[0][2:5] and M.shape==(size,hi-lo)
        cursor=hi
    assert cursor==size
    M=np.column_stack([c[-1] for c in chunks]);v=eigvals(M)
    print('finite history spectrum',size,'rho',max(abs(v)),'unstable',sum(abs(v)>1+1e-5),flush=True)
    print('LIMIT history interpolation and time integration errors not enclosed; compare knot refinements, no infinite-dimensional certificate')
    return M
