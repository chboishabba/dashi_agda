"""Finite source energy ledger and reciprocal phase anchor on actual full RHS.
Ideal controlled effort source, not an atmospheric source constitutive law.
"""
import numpy as np
import sympy as S
from solar_steelman_full_rhs import build


def build_source(m,a):
    base,orbit,rate,power=build(m,a)
    n=len(a['models']); source_index=m['d']['M'].rows+m['d']['N'].rows+m['H'].rows
    def rhs(t,Y,gain=100.,gamma=0.,anchor_gamma=0.,feed=0.):
        y=Y[:-4];phi,q,W,heat=Y[-4:]
        # Rotating reference phase; base RHS has explicit time only in drive.
        if W<=0:raise ValueError('source reservoir exhausted')
        dy=base(t+phi/2,y,gamma,gain)
        p=y[-n:];theta=y[-2*n]-y[-3*n]
        delta=2*theta-2*t-phi;speed=2*p[0]-q
        tau=np.sin(delta)+anchor_gamma*speed
        dy[-n]-=2*tau
        s=np.sqrt(2)*np.cos(2*t+phi);i=y[source_index]
        debit=s*s-(s-i)**2
        diss=gamma*sum((p[j]-p[a['parent'][j]])**2 for j in a['order'][1:])+anchor_gamma*speed**2
        return np.r_[dy,q,tau,feed-debit,diss]
    def total_rate(t,Y,dY):
        y=Y[:-4];phi,q,W,heat=Y[-4:];dy=dY[:-4];dphi,dq,dW,dh=dY[-4:]
        theta=y[-2*n]-y[-3*n];dtheta=dy[-2*n]-dy[-3*n]
        return rate(y,dy)+q*dq+np.sin(2*theta-2*t-phi)*(2*dtheta-2-dphi)+dW+dh
    def useful(Y):
        j=Y[source_index+4:source_index+11];return float(a['rows'][1]['load'])*(j@j)
    def nominal(t,W0=100.):
        # No feed: matched incident work integrates to t+sin(4t)/4.
        return np.r_[orbit(t),0.,0.,W0-t-np.sin(4*t)/4,0.]
    return rhs,total_rate,useful,nominal


def run(m,a):
    p,q,k,g,d=S.symbols('p q k g d',real=True);v=2*p-q;tau=k*S.sin(d)+g*v
    assert S.expand(-2*p*tau+q*tau+k*S.sin(d)*v+g*v*v)==0
    t=S.symbols('t',real=True);assert S.integrate(2*S.cos(2*t)**2,(t,0,2*S.pi))==2*S.pi
    rhs,rate,useful,nominal=build_source(m,a);rng=np.random.default_rng(369);worst=0.;nom=0.
    for t in np.linspace(0,2*np.pi,17):
        Y=nominal(t);dY=rhs(t,Y);nom=max(nom,abs(dY[-4]),abs(dY[-3]),abs(dY[-2]+2*np.cos(2*t)**2),abs(dY[-1]))
        P=Y+.001*rng.normal(size=len(Y));dP=rhs(t,P,gamma=.5,anchor_gamma=.5,feed=.37)
        worst=max(worst,abs(rate(t,P,dP)+useful(P)-.37))
    assert nom<1e-8 and worst<1e-6
    print('PASS actual source-backed RHS dimension',len(Y),'nominal source residual',nom,'perturbed total ledger',worst)
    print('PASS finite source loses exactly 2*pi per nominal period, no unpowered full source return')
    print('LIMIT ideal effort transduction, source phase controller and abstract upstream feed; no natural-source admission')


if __name__=='__main__':
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument('--metric',required=True);p.add_argument('--mediator',required=True);a=p.parse_args()
    with open(a.metric,'rb') as f:m=pickle.load(f)
    with open(a.mediator,'rb') as f:b=pickle.load(f)
    run(m,b)
