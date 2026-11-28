"""Full rotating-state tangent and column-block monodromy on reservoir-backed orbit.
Numerical diagnostics; no physical or interval certification.
"""
import numpy as np
import sympy as S
from scipy.integrate import solve_ivp
from scipy.linalg import eigvals, svdvals
from solar_steelman_variational import construct as core
from solar_steelman_reservoir_return import construct as nonlinear, preflight
from solar_steelman_boundary_weld import branch

def construct(m,a,Wstar=100.,gain=100.,gamma=.5,anchor_gamma=.5):
    g=core(m,a); rhs,target,_,_=nonlinear(m,a,Wstar,gain,gamma,anchor_gamma)
    n,nc,dim=g['n'],g['nc'],g['dim']; L=g['L']; size=nc+5*n+4
    e0,e1,h0,h1,p=[slice(nc+k*n,nc+(k+1)*n) for k in range(5)]
    phi,q,W,heat=range(size-4,size)
    i=m['d']['M'].rows+m['d']['N'].rows+m['H'].rows
    Ls,_=branch(S.Integer(2),S.Integer(1),-a['rows'][0]['X'][:1,:1])
    invL=1/float(Ls[0,0])
    coeff=[{k:complex(v) for k,v in c.items()} for _,_,c in a['models']]
    # Core coordinates are physical field/boundary states and total stores.
    R=np.zeros((dim,size));R[:nc,:nc]=np.eye(nc)
    R[nc:,e0]=R[nc:,e1]=np.eye(n)
    H=np.zeros((n,size));H[:,h1]=np.eye(n);H[:,h0]=-np.eye(n)
    def matrix(t):
        X=target(t);u=np.exp(1j*t)
        es=np.array([sum(v*u**k for k,v in c.items()).real for c in coeff])
        ep=np.array([sum(1j*k*v*u**k for k,v in c.items()).real for c in coeff])
        J,P,_=g['tangent'](t)
        J[nc:,nc:]-=gain*L/es[None,:]
        P[nc:,:]+=gain*L*(ep/es)[None,:]
        C=J@R+P@H
        s=np.sqrt(2)*np.cos(2*t); sp=-np.sqrt(2)*np.sin(2*t); sw=s/(2*Wstar)
        C[i,phi]+=2*invL*sp; C[i,W]+=2*invL*sw
        A=np.zeros((size,size)); A[:nc]=C[:nc]
        # d(e0/e)=(de0-de1)/(2e), nominal total store derivative S'.
        A[e0]=A[e1]=C[nc:]/2
        diag=np.diag(ep/(2*es))
        A[e0,e0]+=diag; A[e0,e1]-=diag
        A[e1,e0]-=diag; A[e1,e1]+=diag
        A[h1,p]=np.eye(n)
        A[p]=-L@H; A[p,p]-=gamma*L
        # anchor at cell zero only; both half-phase branches retained.
        tau=2*H[0].copy();tau[phi]-=1
        tau[p.start]+=2*anchor_gamma;tau[q]-=anchor_gamma
        A[p.start]-=2*tau; A[q]+=tau; A[phi,q]=1
        # W'=feed-2si+i^2, so current derivative vanishes at match.
        A[W,i]=2*(X[i]-s);A[W,phi]=-2*X[i]*sp;A[W,W]=-2*X[i]*sw
        # Quadratic heat production has zero linearization at nominal lock.
        return A
    return rhs,target,matrix

def check(m,a):
    preflight(m,a)
    rhs,target,mat=construct(m,a);rng=np.random.default_rng(369);worst=0.
    for t in np.linspace(0,2*np.pi,9):
        X=target(t);A=mat(t)
        for _ in range(3):
            v=rng.normal(size=len(X));eps=1e-5
            fd=(rhs(t,X+eps*v)-rhs(t,X-eps*v))/(2*eps)
            exact=A@v
            worst=max(worst,np.linalg.norm(fd-exact,np.inf)/max(1,np.linalg.norm(exact,np.inf)))
    assert worst<2e-5,worst
    print("PASS full analytic tangent FD",len(X),worst,flush=True)
    return mat,len(X)

def block(m,a,start,stop,tol,out):
    mat,d=check(m,a)
    if not 0<=start<stop<=d:raise ValueError("invalid column bounds")
    k=stop-start
    sol=solve_ivp(lambda t,y:(mat(t)@y.reshape(d,k)).ravel(),(0,2*np.pi),np.eye(d)[:,start:stop].ravel(),method="DOP853",rtol=tol,atol=tol*.01,t_eval=[2*np.pi])
    if not sol.success:raise RuntimeError(sol.message)
    np.savez(out,M=sol.y[:,-1].reshape(d,k),start=start,stop=stop,tol=tol)
    print("PASS monodromy column block",start,stop,tol,flush=True)

def assemble(paths):
    chunks=[]
    for path in paths:
        with np.load(path,allow_pickle=False) as f:chunks.append((int(f['start']),int(f['stop']),float(f['tol']),f['M']))
    chunks.sort(key=lambda x:x[0]);d=chunks[0][3].shape[0];tol=chunks[0][2];cursor=0
    for start,stop,t,M in chunks:
        assert start==cursor and t==tol and M.shape==(d,stop-start) and np.isfinite(M).all()
        cursor=stop
    assert cursor==d
    M=np.column_stack([x[3] for x in chunks]);v=eigvals(M)
    print("full monodromy",d,tol,"rho",max(abs(v)),"unstable count",sum(abs(v)>1+1e-5),flush=True)
    N=M-np.eye(d)
    for eps in (1e-5,1e-7,1e-9):
        print("numerical +1 nullities",eps,[int(sum(svdvals(B)<eps)) for B in (N,N@N)],flush=True)
    print("LIMIT numerical spectrum and rank sensitivity; no quotient or basin certification",flush=True)

if __name__=="__main__":
    import argparse,pickle
    p=argparse.ArgumentParser()
    p.add_argument("--metric");p.add_argument("--mediator")
    p.add_argument("--start",type=int);p.add_argument("--stop",type=int)
    p.add_argument("--tol",type=float,default=1e-7);p.add_argument("--out")
    p.add_argument("--assemble",nargs="+")
    args=p.parse_args()
    if args.assemble:assemble(args.assemble)
    else:
        with open(args.metric,"rb") as f:m=pickle.load(f)
        with open(args.mediator,"rb") as f:a=pickle.load(f)
        if args.start is None:check(m,a)
        else:block(m,a,args.start,args.stop,args.tol,args.out)
