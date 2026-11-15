#!/usr/bin/env python3
"""Constructive reciprocal time-modulated receiver + finite natural reservoir.
Original DASHI numerical benchmark (normalized units, not Smith hardware).
The environmental oscillator is DYNAMIC, not an imposed voltage source.
"""
from dataclasses import dataclass,asdict
import numpy as np
from scipy.integrate import solve_ivp

@dataclass(frozen=True)
class Model:
    wl:float=3.8
    wc:float=3.85
    we:float=3.78
    gamma_load:float=.27
    gamma_local:float=.035
    gamma_converter:float=.03
    gamma_environment:float=.012
    beta:float=.035
    g_lc:float=.62
    g_ce:float=.36
    driven_strength:float=.13
    natural_strength:float=0.
    environment_initial:float=5.
    until:float=18.
    final:float=24.
    depth:float=.72

def coupling(t,phase,p):
    if t>=p.until:return (0.,0.,0.,0.)
    th=np.pi*t/p.until
    w=np.sin(th)**2
    wd=np.pi/p.until*np.sin(2*th)
    arg=2*p.wl*t+phase
    C=1+p.depth*np.cos(arg)
    Cd=-2*p.wl*p.depth*np.sin(arg)
    g1=p.g_lc*w*C
    dg1=p.g_lc*(wd*C+w*Cd)
    a2=(p.we-p.wc)*t+.37*phase
    C2=1+.32*np.cos(a2)
    g2=p.g_ce*w*C2
    dg2=p.g_ce*(wd*C2-w*.32*(p.we-p.wc)*np.sin(a2))
    return g1,dg1,g2,dg2

def simulate(phase,p=Model()):
    # x receiver, z converter, y environment; velocities and separate work.
    state=np.zeros(12)
    state[2]=p.environment_initial
    def rhs(t,S):
        x,z,y,vx,vz,vy=S[:6]
        g1,dg1,g2,dg2=coupling(t,phase,p)
        d=x-z;q=z-y
        fd=p.driven_strength*np.cos(p.wl*t) if t<p.until else 0.
        fn=p.natural_strength*np.cos(p.we*t+.2)
        ax=-p.wl**2*x-g1*d-(p.gamma_load+p.gamma_local)*vx+fd
        az=-p.wc**2*z+g1*d-g2*q-p.beta*z**3-p.gamma_converter*vz
        ay=-p.we**2*y+g2*q-p.gamma_environment*vy+fn
        modwork=.5*dg1*d*d+.5*dg2*q*q
        loss=p.gamma_local*vx*vx+p.gamma_converter*vz*vz+p.gamma_environment*vy*vy
        return [vx,vz,vy,ax,az,ay,fd*vx,fn*vy,modwork,p.gamma_load*vx*vx,loss,p.gamma_environment*vy*vy]
    res=solve_ivp(rhs,(0,p.final),state,rtol=8e-9,atol=1e-10,max_step=.012)
    if not res.success:raise RuntimeError(res.message)
    def energy(t,S):
        x,z,y,vx,vz,vy=S[:6]
        g1,_,g2,_=coupling(t,phase,p)
        return .5*(vx*vx+vz*vz+vy*vy+(p.wl*x)**2+(p.wc*z)**2+(p.we*y)**2)+p.beta*z**4/4+g1*(x-z)**2/2+g2*(z-y)**2/2
    q=res.y[:,-1]
    e0=energy(0,state);e1=energy(p.final,q)
    wd,wn,wm,use,loss,envloss=map(float,q[6:12])
    env0=.5*(p.we*p.environment_initial)**2
    env1=.5*(q[5]**2+(p.we*q[2])**2)
    return dict(phase=float(phase),driver=wd,natural_recharge=wn,
        controller=wm,useful=use,loss=loss,environment_initial=env0,
        environment_final=float(env1),environment_loss=envloss,
        transferred_from_environment=float(env0+wn-env1-envloss),
        total_initial=float(e0),total_final=float(e1),
        residual=float(e1-e0-wd-wn-wm+use+loss))

def check():
    p=Model();control=Model(**{**asdict(p),'environment_initial':0})
    rows=[]
    for ph in np.arange(0,2*np.pi,np.pi/8):
        a=simulate(ph,p);b=simulate(ph,control)
        assert abs(a['residual'])<3e-6 and abs(b['residual'])<3e-6
        assert a['natural_recharge']==0
        assert a['environment_initial']>a['environment_final']
        assert b['useful']<=b['driver']+b['controller']+1e-5
        a['net_gain_from_reservoir_comparison']=(a['useful']-b['useful'])-(a['driver']+a['controller']-b['driver']-b['controller'])
        rows.append(a)
    assert min(r['net_gain_from_reservoir_comparison'] for r in rows)<0
    assert max(r['net_gain_from_reservoir_comparison'] for r in rows)>0
    positive_paid=rows[4] # pi/2, actuator explicitly draws positive work
    assert positive_paid['controller']>0
    assert positive_paid['useful']>positive_paid['driver']+positive_paid['controller']
    print('PASS 16-phase same-system reciprocal natural-donor and control world; max residue',
          max(abs(x['residual']) for x in rows))
if __name__=='__main__':check()
