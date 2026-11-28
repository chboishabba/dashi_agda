"""Analytic tangent of the same full RHS, conserved fibres and Floquet diagnostic.
Numerical variational evidence only, not an interval or physical certificate.
"""
import numpy as np
import sympy as S
from scipy.linalg import null_space, eigvals
from scipy.integrate import solve_ivp
from solar_steelman_full_rhs import build
from solar_steelman_boundary_weld import branch


def construct(m,a):
    arr=lambda x:np.array(x,dtype=float)
    cx=lambda x:np.array(x,dtype=complex).ravel()
    d=m['d']; M,N,C,B,H=map(arr,(d['M'],d['N'],d['C'],m['B'],m['H']))
    T=arr(d['T']);ts=T[:1];tr=T[8:15];hi,lo=a['rows'];R=float(lo['load'])
    Ls,Ks=map(arr,branch(S.Integer(2),S.Integer(1),-hi['X'][:1,:1]));Lr,Kr=map(arr,branch(S.Integer(1),S.Integer(2),-lo['X'][8:15,8:15]))
    Mi=np.linalg.inv(M);Hi=np.linalg.inv(H)/2;Ls=np.linalg.inv(Ls);Lr=np.linalg.inv(Lr)
    n=len(a['models']);h=(1+1j)/np.sqrt(2)
    sizes=[len(M),len(N),len(H),1,1,1,1,7,7,7,7,n];bounds=np.r_[0,np.cumsum(sizes)]
    E,b,z,i,q,x,v,j,Q,X,V,e=[slice(k,l) for k,l in zip(bounds[:-1],bounds[1:])];dim=bounds[-1];nc=bounds[-2]
    I=np.eye(dim);A=np.zeros((dim,dim))
    A[E,b]=Mi@C.T@N;A[E,z]=-Mi@B;A[E,i]=Mi@ts.T;A[E,j]=-Mi@tr.T
    A[b,E]=-C;A[z,E]=Hi@B.T
    A[i,E]=-Ls@ts;A[i,i]=-Ls;A[i,q]=-Ls@Ks;A[i,x]=-Ls
    A[q,i]=I[q,q];A[x,i]=I[x,i];A[x,v]=-I[x,x];A[v,x]=I[v,v]
    A[j,E]=Lr@tr;A[j,j]=-R*Lr;A[j,Q]=-Lr@Kr;A[j,X]=-Lr
    A[Q,j]=I[Q,Q];A[X,j]=I[X,X];A[X,V]=-4*I[X,X];A[V,X]=I[V,V]
    models=[(np.array(ids),{w:cx(r[w][0]+S.I*r[w][1]) for w in (1,2)},{k:complex(v) for k,v in c.items()}) for ids,r,c in a['models']]
    edges=[(a['parent'][l],l,float(a['flows'][l])) for l in a['order'][1:]]
    zp={w:cx(a['data'][w][0][0]+S.I*a['data'][w][0][1]) for w in (1,2)}
    D=np.zeros((n,n-1))
    for col,(k,l,_) in enumerate(edges):D[k,col]=-1;D[l,col]=1
    L=D@D.T
    def tangent(t):
        u=np.exp(1j*t);zt=np.sqrt(2)*(zp[2]*u**2+h*zp[1]*u).real
        es=np.array([sum(v*u**k for k,v in c.items()).real for _,_,c in models])
        ep=np.array([sum(1j*k*v*u**k for k,v in c.items()).real for _,_,c in models])
        J=A.copy();P=np.zeros((dim,n));F=np.zeros((len(H),n))
        for k,(ids,r,c) in enumerate(models):
            f=np.sqrt(2)*(r[2]*u**2+h*r[1]*u).real
            fp=np.sqrt(2)*(2j*r[2]*u**2+1j*h*r[1]*u).real
            # d lambda = (d e - S'(theta) d theta)/S(theta)
            dtheta=fp-f*ep[k]/es[k]
            F[ids,k]=f
            J[z,nc+k]+=Hi[:,ids]@f/es[k];P[z,k]+=Hi[:,ids]@dtheta
            J[nc+k,z.start+ids]-=f
            J[nc+k,nc+k]-=zt[ids]@f/es[k];P[nc+k,k]-=zt[ids]@dtheta
        for k,l,flow in edges:
            for row,sgn in ((k,-1),(l,1)):
                for col in (k,l):
                    J[nc+row,nc+col]+=sgn*flow/es[col]
                    P[nc+row,col]-=sgn*flow*ep[col]/es[col]
        return J,P,F
    def reduce(y):return np.r_[y[:nc],y[nc:nc+n]+y[nc+n:nc+2*n]]
    def lift(dy,phase):
        return np.r_[dy[:nc],dy[nc:]/2,dy[nc:]/2,np.zeros(n),phase,np.zeros(n)]
    rhs,orbit,rate,power=build(m,a)
    return dict(tangent=tangent,reduce=reduce,lift=lift,rhs=rhs,orbit=orbit,L=L,B=B,C=C,N=N,H=H,n=n,nc=nc,dim=dim,z=z,b=b)


def certify(m,a,floquet=False):
    g=construct(m,a);Jfun=g['tangent'];n=g['n'];dim=g['dim'];nc=g['nc'];rng=np.random.default_rng(369)
    worst=0.;inv=0.;null_defect=0.;Z=null_space(g['B']);W=null_space(g['C'].T)
    for t in np.linspace(0,2*np.pi,9):
        J,P,F=Jfun(t);y=g['orbit'](t);d=rng.normal(size=dim);theta=rng.normal(size=n);v=g['lift'](d,theta);eps=1e-5
        actual=g['reduce']((g['rhs'](t,y+eps*v)-g['rhs'](t,y-eps*v))/(2*eps))
        target=J@d+P@theta;worst=max(worst,np.linalg.norm(actual-target,np.inf)/max(1,np.linalg.norm(target,np.inf)))
        inv=max(inv,np.linalg.norm(W.T@J[g['b'],:],np.inf))
        null_defect=max(null_defect,np.linalg.norm(Z.T@F,np.inf))
    assert worst<2e-5 and inv<1e-9 and null_defect>1e-6
    print('PASS analytic tangent core',dim,'phase forcing',n,'relative FD error',worst,flush=True)
    print('magnetic left invariant count',W.shape[1],'residual',inv,'material null dimension',Z.shape[1],'nonzero local force contraction',null_defect,flush=True)
    # Local lower phase rotations and energy fractions are exact invariants
    # from rhs: dot theta0=Omega, dot(e0/(e0+e1))=0; beat/momentum subsystem
    # independent of core. Common momentum produces a Jordan drift in phase.
    L=g['L'];ev=np.linalg.eigvalsh(L);assert np.count_nonzero(ev>1e-9)==47
    print('PASS independent phase subsystem 47 relative modes; common phase/momentum Jordan drift; 48 ratios and 48 lower phase offsets',flush=True)
    # Fixed independent source phase means common beat phase is not a global
    # time-translation symmetry of the forced complete system. Retain its
    # forcing column P rather than claiming a semisimple neutral full mode.
    print('common beat forcing norm',np.linalg.norm(Jfun(.37)[1]@np.ones(n)),flush=True)
    if not floquet:return
    # Magnetic left invariants can be removed for the homogeneous core
    # restriction (zero perturbation of invariant values); other coordinates
    # retained. Use Euclidean orthonormal basis for b in im(C).
    from scipy.linalg import orth
    U=orth(g['C']);keep=np.eye(dim)[:,:g['b'].start]
    mid=np.zeros((dim,U.shape[1]));mid[g['b'],:]=U
    tail=np.eye(dim)[:,g['b'].stop:];Q=np.column_stack((keep,mid,tail));dQ=Q.shape[1]
    def mat(t):return Q.T@Jfun(t)[0]@Q
    def integrate(rtol):
        sol=solve_ivp(lambda t,Y:(mat(t)@Y.reshape(dQ,dQ)).ravel(),(0,2*np.pi),np.eye(dQ).ravel(),method='DOP853',rtol=rtol,atol=rtol*0.01)
        assert sol.success
        P=sol.y[:,-1].reshape(dQ,dQ);rho=max(abs(eigvals(P)))
        print('Floquet core numerical',dQ,'rtol',rtol,'steps',len(sol.t),'rho',rho,flush=True)
        return P,rho
    P,rho=integrate(1e-7);Q2,rho2=integrate(1e-9)
    print('Floquet refinement relative matrix error',np.linalg.norm(P-Q2)/max(1,np.linalg.norm(Q2)),'rho difference',abs(rho-rho2),flush=True)
    print('Diagnostic only: no interval enclosure or all-state physical stability certificate',flush=True)

if __name__=='__main__':
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument('--metric');p.add_argument('--mediator');p.add_argument('--floquet',action='store_true');args=p.parse_args()
    if args.metric and args.mediator:
        # Only load trusted locally generated checkpoints.
        with open(args.metric,'rb') as f:m=pickle.load(f)
        with open(args.mediator,'rb') as f:a=pickle.load(f)
    else:
        from solar_steelman_material_metric import run as metric
        from solar_steelman_autonomous_mediator import run as mediator
        m=metric();a=mediator(m)
    certify(m,a,args.floquet)
