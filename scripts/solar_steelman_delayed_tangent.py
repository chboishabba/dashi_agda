"""Analytic delay tangent on the occupied retarded face return.
Finite history discretization is a diagnostic, not a certified delay spectrum.
"""
import numpy as np
from scipy.integrate import solve_ivp
from solar_steelman_anchored_monodromy import construct as instant
from solar_steelman_retarded_face_return import build as delayed

def construct(m,a,delay=.01,gain=100.):
    if delay<=0:raise ValueError('positive delay')
    _,target,mat=instant(m,a,gain=gain)
    n=len(a['models']);d=len(target(0));nc=d-5*n-4
    edges=[(a['parent'][j],j,float(a['flows'][j])) for j in a['order'][1:]]
    if any(f==0 for _,_,f in edges):
        raise ValueError('zero nominal face flow: positive-part kink needs directional analysis')
    coeff=[{k:complex(v) for k,v in c.items()} for _,_,c in a['models']]
    # Derivative of e/S(theta), evaluated on occupied orbit.
    def R(t):
        u=np.exp(1j*t)
        s=np.array([sum(v*u**k for k,v in c.items()).real for c in coeff])
        sp=np.array([sum(1j*k*v*u**k for k,v in c.items()).real for c in coeff])
        out=np.zeros((n,d))
        for k in range(n):
            out[k,nc+k]=out[k,nc+n+k]=1/s[k]
            out[k,nc+2*n+k]=sp[k]/s[k]
            out[k,nc+3*n+k]=-sp[k]/s[k]
        return out
    size=d+2*len(edges)
    def matrices(t):
        r=[R(t-k*delay) for k in range(3)]
        A=[np.zeros((size,size)) for _ in range(3)]
        A[0][:d,:d]=mat(t)
        def cell(B,j,v):
            B[nc+j,:d]+=v/2;B[nc+n+j,:d]+=v/2
        for e,(k,l,f) in enumerate(edges):
            # Remove instantaneous signed flux derivative.
            old=(f+gain)*r[0][k]+(f-gain)*r[0][l]
            cell(A[0],k,old);cell(A[0],l,-old)
            # The occupied sign determines the differentiable active
            # directed branch. Flight energy is a dependent ledger.
            src,dst,F,idx=(k,l,f,2*e) if f>0 else (l,k,-f,2*e+1)
            launch_now=(F+gain)*r[0][src]
            launch_past=(F-gain)*r[1][dst]
            arrival_past=(F+gain)*r[1][src]
            arrival_older=(F-gain)*r[2][dst]
            cell(A[0],src,-launch_now);cell(A[1],src,-launch_past)
            cell(A[1],dst,arrival_past);cell(A[2],dst,arrival_older)
            A[0][d+idx,:d]+=launch_now
            A[1][d+idx,:d]+=launch_past-arrival_past
            A[2][d+idx,:d]-=arrival_older
        return A
    rhs,orbit,_=delayed(m,a,delay,gain)
    return matrices,rhs,orbit

def check(m,a,delay=.01):
    mat,rhs,orbit=construct(m,a,delay)
    rng=np.random.default_rng(369);err=0.
    for t in np.linspace(0,2*np.pi,9):
        Y=orbit(t);d=len(Y);v=rng.normal(size=(3,d));eps=1e-6
        # Independent perturbations of three samples of delay history.
        def history(s,sign):
            k=int(round((t-s)/delay));assert k in (1,2)
            return orbit(s)+sign*eps*v[k]
        fd=(rhs(t,Y+eps*v[0],lambda s:history(s,1))-rhs(t,Y-eps*v[0],lambda s:history(s,-1)))/(2*eps)
        ref=sum(A@x for A,x in zip(mat(t),v))
        err=max(err,np.linalg.norm(fd-ref,np.inf)/max(1.,np.linalg.norm(ref,np.inf)))
    assert err<2e-5,err
    print('PASS full delayed tangent directional FD',d,delay,err,flush=True)
    return mat,orbit

def history_action(m,a,delay=.01,tol=1e-7,periods=1,seed=369):
    mat,orbit=check(m,a,delay)
    d=len(orbit(0));rng=np.random.default_rng(seed)
    # Continuous test history, not a complete history basis.
    a0=rng.normal(size=d);a1=rng.normal(size=d)
    def initial(t):return a0*np.cos(t)+a1*np.sin(t)
    pieces=[];Y=initial(0);t=0.;T=periods*2*np.pi
    def hist(s):
        if s<=0:return initial(s)
        for lo,hi,sol in reversed(pieces):
            if lo-1e-12<=s<=hi+1e-12:return sol(min(hi,max(lo,s)))
        raise RuntimeError('history gap')
    def f(s,y):
        A,B,C=mat(s)
        return A@y+B@hist(s-delay)+C@hist(s-2*delay)
    while t<T-1e-12:
        end=min(T,t+delay)
        sol=solve_ivp(f,(t,end),Y,rtol=tol,atol=tol*.01,method='DOP853',dense_output=True)
        if not sol.success:raise RuntimeError(sol.message)
        pieces.append((t,end,sol.sol));Y=sol.y[:,-1];t=end
    before=max(np.linalg.norm(initial(s)) for s in np.linspace(-2*delay,0,33))
    after=max(np.linalg.norm(hist(s)) for s in np.linspace(T-2*delay,T,33))
    print('sampled history action ratio',after/before,'seed',seed,'periods',periods,flush=True)
    print('LIMIT single unconstrained history perturbation; flight ledger consistency, invariant leaf, operator norm and delay spectral enclosures not certified')
