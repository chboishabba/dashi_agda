"""Conservative energy redistribution on actual shared-face store graph.
Zero on the nominal orbit. Numerical Floquet diagnostics, not interval proof.
"""
import numpy as np
from scipy.linalg import orth,eig,svdvals
from scipy.integrate import solve_ivp
from solar_steelman_variational import construct


def correction(energy,target,edges,gain):
    """Positive-domain exchange: edge flux gain*(lambda_i-lambda_j).
    Flow vanishes at lambda_i=lambda_j; total stored energy unchanged.
    At a zero-energy boundary every incident correction points inward.
    """
    ratio=energy/target;de=np.zeros_like(energy)
    for i,j in edges:
        f=gain*(ratio[i]-ratio[j]);de[i]-=f;de[j]+=f
    return de


def run(m,a):
    g=construct(m,a);dim,n,nc=g['dim'],g['n'],g['nc'];L=g['L'];Jfun=g['tangent'];b=g['b']
    U=orth(g['C']);mid=np.zeros((dim,U.shape[1]));mid[b,:]=U
    Q=np.column_stack((np.eye(dim)[:,:b.start],mid,np.eye(dim)[:,b.stop:]));d=Q.shape[1]
    coefficients=[{k:complex(v) for k,v in c.items()} for _,_,c in a['models']]
    def target(t):
        u=np.exp(1j*t);return np.array([sum(v*u**k for k,v in c.items()).real for c in coefficients])
    edges=[(a['parent'][j],j) for j in a['order'][1:]]
    for t in np.linspace(0,2*np.pi,9):
        e=target(t);assert min(e)>0 and np.array_equal(correction(e,e,edges,1),np.zeros(n))
        rng=np.random.default_rng(369);v=rng.random(n)*e;v[0]=0
        c=correction(v,e,edges,1);assert abs(sum(c))<1e-12 and c[0]>=0
        assert np.allclose(c,-L@(v/e))
    # Exact edge algebra independent of floating-point fixture: each edge
    # contributes (-f,+f), zero sum, and at e_i=0 its derivative is +g e_j/S_j.
    import sympy as S
    x,y,A,B,k=S.symbols('x y A B k',nonnegative=True);f=k*(x/A-y/B)
    assert S.expand(-f+f)==0 and S.simplify(-f.subs(x,0)-k*y/B)==0
    print('PASS conservative store redistribution, nominal zero, positive-domain boundary',flush=True)
    def integrate(gain,tol=1e-7):
        def mat(t):
            J=Jfun(t)[0];J[nc:,nc:]-=gain*L/target(t)[None,:]
            return Q.T@J@Q
        sol=solve_ivp(lambda t,Y:(mat(t)@Y.reshape(d,d)).ravel(),(0,2*np.pi),np.eye(d).ravel(),method='DOP853',rtol=tol,atol=tol*.01)
        assert sol.success
        P=sol.y[:,-1].reshape(d,d);vals,vec=eig(P);idx=np.argmax(abs(vals));v=Q@vec[:,idx]
        rho=abs(vals[idx]);count=np.count_nonzero(abs(vals)>1.00001)
        print('gain',gain,'tol',tol,'rho',rho,'unstable count',count,'dominant',vals[idx],'store fraction',np.linalg.norm(v[nc:])/np.linalg.norm(v),flush=True)
        return rho,count
    # Declared finite witness gain, not a physical resource calibration.
    gain=100
    worst=0.;rng=np.random.default_rng(369)
    for t in np.linspace(0,2*np.pi,9):
        J,P,_=Jfun(t);J[nc:,nc:]-=gain*L/target(t)[None,:]
        y=g['orbit'](t);dvec=rng.normal(size=dim);theta=rng.normal(size=n);v=g['lift'](dvec,theta);eps=1e-5
        actual=g['reduce']((g['rhs'](t,y+eps*v,0,gain)-g['rhs'](t,y-eps*v,0,gain))/(2*eps))
        # Target derivative with respect to phase: d(lambda)=-S'/S dtheta.
        u=np.exp(1j*t);ep=np.array([sum(1j*k*v*u**k for k,v in c.items()).real for c in coefficients])
        P[nc:,:]+=gain*L*(ep/target(t))[None,:]
        wanted=J@dvec+P@theta
        worst=max(worst,np.linalg.norm(actual-wanted,np.inf)/max(1,np.linalg.norm(wanted,np.inf)))
        assert np.array_equal(g['rhs'](t,y,0,gain),g['rhs'](t,y)) or np.allclose(g['rhs'](t,y,0,gain),g['rhs'](t,y),rtol=0,atol=1e-10)
    assert worst<2e-5
    print('PASS actual modified RHS tangent, relative FD error',worst,flush=True)
    from solar_steelman_full_rhs import build
    rhs,orbit,rate,power=build(m,a);err=0.
    for t in np.linspace(0,2*np.pi,9):
        y=orbit(t)+.001*rng.normal(size=len(orbit(t)))
        err=max(err,abs(rate(y,rhs(t,y,.5,gain))-power(t,y,.5)))
    assert err<1e-6
    print('PASS actual modified RHS perturbed energy ledger',err,flush=True)
    base=integrate(0);coarse=integrate(gain);fine=integrate(gain,1e-9)
    assert base[0]>1.01 and coarse[1]==0 and fine[1]==0
    print('LIMIT numerical spectrum only; neutral Jordan chains, absolute phase anchoring and physical transport not certified',flush=True)

if __name__=='__main__':
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument('--metric');p.add_argument('--mediator');args=p.parse_args()
    if args.metric and args.mediator:
        with open(args.metric,'rb') as f:m=pickle.load(f)
        with open(args.mediator,'rb') as f:a=pickle.load(f)
    else:
        from solar_steelman_material_metric import run as metric
        from solar_steelman_autonomous_mediator import run as mediator
        m=metric();a=mediator(m)
    run(m,a)
