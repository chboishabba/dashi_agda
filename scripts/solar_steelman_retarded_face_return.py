"""Finite-delay realization of the existing shared-face port law.
Method of steps on the same reservoir-backed model, not a Maxwell realization.
"""
import numpy as np
from scipy.integrate import solve_ivp
from solar_steelman_reservoir_return import construct as base
from solar_steelman_carrier_mediator import OMEGA

def build(m,a,delay=.01,gain=100.):
    if delay<=0:raise ValueError("positive flight duration required")
    rhs,target,_,ledger=base(m,a,gain=gain)
    n=len(a['models']);d=len(target(0));nc=d-5*n-4
    e0=slice(nc,nc+n);e1=slice(nc+n,nc+2*n)
    h0=slice(nc+2*n,nc+3*n);h1=slice(nc+3*n,nc+4*n)
    coeff=[{k:complex(v) for k,v in c.items()} for _,_,c in a['models']]
    edges=[(a['parent'][j],j,float(a['flows'][j])) for j in a['order'][1:]]
    def ratios(t,X):
        u=np.exp(1j*(t+X[h1]-X[h0]))
        S=np.array([sum(v*u[k]**j for j,v in c.items()).real for k,c in enumerate(coeff)])
        return (X[e0]+X[e1])/S
    def launches(t,X,Xpast):
        r=ratios(t,X);p=ratios(t-delay,Xpast)
        # Each directed launch reads local current and remote delayed state.
        # At zero delay, net launch recovers original signed flow exactly.
        return np.array([[max(0.,f*r[k]*p[l]+gain*(r[k]-p[l])),
                          max(0.,-f*r[l]*p[k]+gain*(r[l]-p[k]))]
                         for k,l,f in edges])
    flight0=delay*np.array([[max(f,0.),max(-f,0.)] for _,_,f in edges])
    def full_target(t):return np.r_[target(t),flight0.ravel()]
    def full_rhs(t,Y,history):
        X=Y[:d];xp=history(t-delay)[:d];xpp=history(t-2*delay)[:d]
        launch=launches(t,X,xp);arrive=launches(t-delay,xp,xpp)
        dy=rhs(t,X);r=ratios(t,X);de=np.zeros(n)
        for edge,(k,l,f) in enumerate(edges):
            old=f*r[k]*r[l]+gain*(r[k]-r[l])
            de[k]+=old-launch[edge,0]+arrive[edge,1]
            de[l]+=-old-launch[edge,1]+arrive[edge,0]
        e=X[e0]+X[e1]
        dy[e0]+=de*X[e0]/e;dy[e1]+=de*X[e1]/e
        return np.r_[dy,(launch-arrive).ravel()]
    def check(t,Y,history):
        dy=full_rhs(t,Y,history)
        return ledger(t,Y[:d],dy[:d])+sum(dy[d:])
    return full_rhs,full_target,check

def run(m,a,delay=.01,tol=1e-7,periods=1,perturb=0.,integrate=False):
    rhs,target,ledger=build(m,a,delay)
    for t in np.linspace(0,2*np.pi,9):
        Y=target(t);d=rhs(t,Y,target)
        assert abs(ledger(t,Y,target))<1e-6
        rng=np.random.default_rng(369)
        P=Y+1e-5*rng.normal(size=len(Y));assert abs(ledger(t,P,target))<1e-6
        eps=1e-5;ref=(target(t+eps)-target(t-eps))/(2*eps)
        assert np.linalg.norm(d-ref,np.inf)/max(1,np.linalg.norm(ref,np.inf))<2e-5
    print("PASS delayed nominal and perturbed combined ledger",len(Y),"flight coordinates",flush=True)
    if not integrate:return
    # Perturb only initial dynamic state; initial in-flight ledger and past
    # history remain the occupied prehistory. This is a startup jump test.
    Y=target(0);d0=len(Y)-2*(len(a['order'])-1)
    Y[:d0]+=perturb*np.random.default_rng(369).normal(size=d0)
    pieces=[];T=2*np.pi*periods;t=0.
    def history(s):
        if s<0:return target(s)
        if not pieces:
            if abs(s)<1e-12:return Y
            raise RuntimeError("future history read")
        for lo,hi,sol in reversed(pieces):
            if lo-1e-12<=s<=hi+1e-12:return sol(min(hi,max(lo,s)))
        raise RuntimeError("history gap")
    while t<T-1e-12:
        end=min(T,t+delay)
        sol=solve_ivp(lambda s,z:rhs(s,z,history),(t,end),Y,rtol=tol,atol=tol*.01,method="DOP853",dense_output=True)
        if not sol.success:raise RuntimeError(sol.message)
        pieces.append((t,end,sol.sol));Y=sol.y[:,-1];t=end
    print("delayed return diagnostic",delay,tol,perturb,np.linalg.norm(Y-target(T),np.inf),flush=True)
    print("LIMIT finite-time return only; delay history monodromy is not the instantaneous 599-state monodromy")

if __name__=="__main__":
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument("--metric",required=True);p.add_argument("--mediator",required=True)
    p.add_argument("--delay",type=float,default=.01);p.add_argument("--tol",type=float,default=1e-7)
    p.add_argument("--periods",type=int,default=1);p.add_argument("--perturb",type=float,default=0.)
    p.add_argument("--integrate",action="store_true");x=p.parse_args()
    with open(x.metric,"rb") as f:m=pickle.load(f)
    with open(x.mediator,"rb") as f:a=pickle.load(f)
    run(m,a,x.delay,x.tol,x.periods,x.perturb,x.integrate)
