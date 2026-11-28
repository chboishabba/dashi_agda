"""Reservoir-amplitude weld on actual 599-state source RHS.
Conditional ideal transducer; not a natural-source admission or stability proof.
"""
import numpy as np
import sympy as S
from scipy.integrate import solve_ivp
from solar_steelman_source_backreaction import build_source
from solar_steelman_boundary_weld import branch
from solar_steelman_full_rhs import build
from solar_steelman_carrier_mediator import OMEGA

def construct(m,a,Wstar=100.,gain=100.,gamma=.5,anchor_gamma=.5):
    if Wstar<=0: raise ValueError("positive reference reservoir required")
    old,rate,useful,nominal=build_source(m,a)
    _,orbit,_,_=build(m,a)
    n=len(a['models'])
    idx=m['d']['M'].rows+m['d']['N'].rows+m['H'].rows
    L,_=branch(S.Integer(2),S.Integer(1),-a['rows'][0]['X'][:1,:1])
    invL=1/float(L[0,0])
    # Rotate both carrier phases, retaining all 96 coordinates and offsets.
    shift=np.zeros(len(nominal(0)))
    shift[-4-3*n:-4-2*n]=float(OMEGA)
    shift[-4-2*n:-4-n]=float(OMEGA)+1
    def rhs(t,X,replenished=True):
        Y=X+t*shift
        W=Y[-2];phi=Y[-4];i=Y[idx]
        if W<=0: raise ValueError("reservoir exhausted: interior model only")
        s0=np.sqrt(2)*np.cos(2*t+phi)
        s=s0*np.sqrt(W/Wstar)
        # Prescribed independent periodic upstream work, not state feedback.
        feed=2*np.cos(2*t)**2 if replenished else 0.
        dY=old(t,Y,gain,gamma,anchor_gamma,feed)
        dY[idx]+=2*invL*(s-s0)
        dY[-2]-=2*i*(s-s0)
        return dY-shift
    def target(t):
        Y=nominal(t);Y[-2]=Wstar
        return Y-t*shift
    def ledger(t,X,dX,replenished=True):
        Y=X+t*shift; dY=dX+shift
        feed=2*np.cos(2*t)**2 if replenished else 0.
        return rate(t,Y,dY)+useful(Y)-feed
    def derivative(t):
        return np.r_[orbit(t,True),0.,0.,0.,0.]-shift
    return rhs,target,derivative,ledger

def preflight(m,a):
    rhs,target,derivative,ledger=construct(m,a)
    rng=np.random.default_rng(369)
    er=el=0.
    for t in np.linspace(0,2*np.pi,17):
        X=target(t);d=rhs(t,X)
        er=max(er,np.linalg.norm(d-derivative(t),np.inf)/max(1,np.linalg.norm(derivative(t),np.inf)))
        P=X+.0001*rng.normal(size=len(X))
        for feed in (True,False):
            el=max(el,abs(ledger(t,P,rhs(t,P,feed),feed)))
    assert er<1e-8 and el<1e-6,(er,el)
    print("PASS reservoir amplitude and full energy preflight",len(X),er,el,flush=True)
    return rhs,target

def integrate(m,a,tol=1e-7,perturb=0.,periods=1):
    rhs,target=preflight(m,a)
    X0=target(0);rng=np.random.default_rng(369)
    X0=X0+perturb*rng.normal(size=len(X0))
    T=2*np.pi*periods
    sol=solve_ivp(rhs,(0,T),X0,method="DOP853",rtol=tol,atol=tol*.01,t_eval=[T])
    if not sol.success: raise RuntimeError(sol.message)
    X=sol.y[:,-1];ref=target(T)
    # Heat is a ledger coordinate; all remaining coordinates retained here.
    err=np.linalg.norm((X-ref)[:-1],np.inf)
    print("return diagnostic",tol,perturb,periods,err,"heat increment",X[-1]-X0[-1],"reservoir",X[-2],flush=True)
    if perturb==0: assert err<max(1e-4,1000*tol)
    print("LIMIT finite-time diagnostic, no basin or Floquet certification",flush=True)

if __name__=="__main__":
    import argparse,pickle
    p=argparse.ArgumentParser()
    p.add_argument("--metric",required=True);p.add_argument("--mediator",required=True)
    p.add_argument("--integrate",action="store_true");p.add_argument("--tol",type=float,default=1e-7)
    p.add_argument("--perturb",type=float,default=0.);p.add_argument("--periods",type=int,default=1)
    args=p.parse_args()
    with open(args.metric,"rb") as f:m=pickle.load(f)
    with open(args.mediator,"rb") as f:a=pickle.load(f)
    if args.integrate:integrate(m,a,args.tol,args.perturb,args.periods)
    else:preflight(m,a)
