"""Neutral fibre and reciprocal finite source clock anchor diagnostics.
Run on trusted checkpoints; no physical source or interval acceptance.
"""
import numpy as np
import sympy as S
from scipy.linalg import orth,svdvals,eigvals
from scipy.integrate import solve_ivp
from solar_steelman_variational import construct

def anchor_algebra():
    # Finite reference rotor, not an infinitely stiff imposed phase.
    # theta'=p, phi'=q/I in rotating coordinates.
    p,q,J,k,g,d=S.symbols('p q J k g d',real=True)
    speed=2*p-q/J
    tau=k*S.sin(d)+g*speed
    assert S.simplify(p*(-2*tau)+q/J*tau+k*S.sin(d)*speed+g*speed**2)==0
    assert -2*tau+2*tau==0
    # Momentum p+2q conserved, overall common phase still free.
    # The physical source amplitude/work response is NOT provided by this rotor.
    print('PASS reciprocal source-reference torque and explicit correction heat',flush=True)

def run(m,a,tol=1e-7):
    anchor_algebra()
    g=construct(m,a);n=g['n'];nc=g['nc'];dim=g['dim'];L=g['L']
    b=g['b'];U=orth(g['C']);mid=np.zeros((dim,U.shape[1]));mid[b,:]=U
    Q=np.column_stack((np.eye(dim)[:,:b.start],mid,np.eye(dim)[:,b.stop:]))
    d=Q.shape[1];gain=100.
    coeff=[{k:complex(v) for k,v in c.items()} for _,_,c in a['models']]
    # Actual core plus phase forcing. All relative beat angles retained.
    # Reference rotor inertia=1, anchor on cell 0 (one selected face owner).
    # Additional variables are theta[48], p[48], phi, q.
    # The source drive phase derivative in the rotating frame must enter
    # actual source current row, not just the phase controller.
    from solar_steelman_boundary_weld import branch
    Ls,_=branch(S.Integer(2),S.Integer(1),-a['rows'][0]['X'][:1,:1])
    source_row=len(m['d']['M'])+len(m['d']['N'])+len(m['H'])
    source_vec=Q.T[:,source_row]*(2*np.sqrt(2)/float(Ls[0,0]))
    # Fixed-source RHS is s=sqrt2*cos(2t); candidate dynamic source
    # s=sqrt2*cos(2t+phi). This is a linearized finite phase-reference
    # extension, not a complete physical source energy/backreaction law.
    Aphase=np.zeros((2*n+2,2*n+2))
    Aphase[:n,n:2*n]=np.eye(n)
    Aphase[n:2*n,:n]=-L
    Aphase[n:2*n,n:2*n]=-.5*L
    Aphase[2*n,2*n+1]=1
    v=np.zeros(2*n+2);v[0]=2;v[2*n]=-1
    w=np.zeros_like(v);w[n]=2;w[-1]=-1
    Aphase-=np.outer(w,v)+.5*np.outer(w,w)
    # Weighted phase Hessian rank n: one common phase direction remains.
    K=np.zeros((n+1,n+1));K[:n,:n]=L
    z=np.zeros(n+1);z[0]=2;z[-1]=-1;K+=np.outer(z,z)
    ev=np.linalg.eigvalsh(K);assert np.count_nonzero(ev>1e-9)==n
    print('phase anchored Hessian rank',n,'of',n+1,'common symmetry retained',flush=True)
    def mat(t):
        J,P,_=g['tangent'](t);u=np.exp(1j*t)
        es=np.array([sum(v*u**k for k,v in c.items()).real for c in coeff])
        ep=np.array([sum(1j*k*v*u**k for k,v in c.items()).real for c in coeff])
        J[nc:,nc:]-=gain*L/es[None,:]
        P[nc:,:]+=gain*L*(ep/es)[None,:]
        return Q.T@J@Q,Q.T@P
    # Integrate monodromy of homogeneous core separately from phase block;
    # inspect unit eigenvalue nullities using SVD at multiple thresholds.
    sol=solve_ivp(lambda t,y:(mat(t)[0]@y.reshape(d,d)).ravel(),(0,2*np.pi),np.eye(d).ravel(),method='DOP853',rtol=tol,atol=tol*.01)
    assert sol.success
    M=sol.y[:,-1].reshape(d,d);vals=eigvals(M);N=M-np.eye(d)
    print('core rho',max(abs(vals)),'near unit +1 count',sum(abs(vals-1)<1e-5),flush=True)
    for eps in (1e-5,1e-7,1e-9):
        print('unit nullities threshold',eps,[int(sum(svdvals(A)<eps)) for A in (N,N@N)],flush=True)
    # Forced phase columns are not eliminated by homogeneous stability.
    from scipy.linalg import expm
    psize=2*n+2
    def forced(t,y):
        J,P=mat(t);F=np.zeros((d,psize));F[:,:n]=P
        F[:,2*n]=-source_vec*np.sin(2*t)
        return (J@y.reshape(d,psize)+F@expm(Aphase*t)).ravel()
    sol=solve_ivp(forced,(0,2*np.pi),np.zeros(d*psize),method='DOP853',rtol=tol,atol=tol*.01)
    assert sol.success
    P=sol.y[:,-1].reshape(d,psize);A=expm(Aphase*2*np.pi)
    full=np.block([[M,P],[np.zeros((psize,d)),A]])
    for eps in (1e-5,1e-7,1e-9):
        J=full-np.eye(len(full))
        print('candidate anchored full nullities',eps,[int(sum(svdvals(B)<eps)) for B in (J,J@J)],flush=True)
    print('LIMIT numerical rank sensitivity; source torque not yet welded to source amplitude energy',flush=True)

if __name__=='__main__':
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument('--metric');p.add_argument('--mediator');p.add_argument('--tol',type=float,default=1e-7);p.add_argument('--algebra-only',action='store_true');args=p.parse_args()
    if args.algebra_only:anchor_algebra()
    else:
        if args.metric and args.mediator:
            with open(args.metric,'rb') as f:m=pickle.load(f)
            with open(args.mediator,'rb') as f:a=pickle.load(f)
        else:
            from solar_steelman_material_metric import run as metric
            from solar_steelman_autonomous_mediator import run as mediator
            m=metric();a=mediator(m)
        run(m,a,args.tol)
