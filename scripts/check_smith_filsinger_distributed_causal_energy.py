#!/usr/bin/env python3
"""Finite spatial Maxwell/telegrapher analogue with explicitly paid plasma-control.
Not the physical atmosphere, and an LC ODE grid does NOT have a strict
continuum light cone. Source-recharge forcing is independently stipulated.
Attribution: user-origin Smith/Filsinger solar-source steelman; DASHI model.
"""
from dataclasses import dataclass, replace
from math import isfinite, pi, sin
import json
import numpy as np
from scipy.integrate import solve_ivp

@dataclass(frozen=True)
class Model:
    nodes: int = 5
    c_node: float = 1.0
    l_link: float = 1.0
    r_link: float = 0.08
    c_source: float = 2.0
    g_recharge: float = 0.3
    g_feed: float = 0.4
    g_load: float = 0.12
    g_plasma_per_n: float = 0.02
    n_init: float = 0.2
    pair_energy: float = 0.5
    ion_seed: float = 0.2
    ion_driven: float = 0.0
    attachment: float = 0.6
    recombination: float = 0.1
    controller_aux: float = 0.0
    exogenous_dc: float = 2.0
    exogenous_ac: float = 0.3
    exogenous_freq: float = 0.7
    delay: float = 0.4
    plasma_node: int = 2
    plasma_mode: str = 'shunt'  # 'series' inserts a variable resistor on link

ENERGY_KEYS=('upstream_input','recharge_heat','feed_heat','link_heat',
             'plasma_heat','load','ion_creation_paid','ion_loss','controller_input',
             'controller_loss')

def validate(p):
    if p.plasma_mode not in ('shunt','series'):
        raise ValueError('unknown plasma placement')
    if p.nodes < 3 or not 0 <= p.plasma_node < p.nodes:
        raise ValueError('bad discrete geometry')
    pos=(p.c_node,p.l_link,p.c_source,p.pair_energy)
    nonneg=(p.r_link,p.g_recharge,p.g_feed,p.g_load,p.g_plasma_per_n,
            p.n_init,p.ion_seed,p.ion_driven,p.attachment,p.recombination,
            p.controller_aux,p.exogenous_freq,p.delay)
    if p.plasma_mode == 'series' and p.plasma_node >= p.nodes-1:
        raise ValueError('series channel must lie on a link')
    if not all(isfinite(x) and x>0 for x in pos) or not all(isfinite(x) and x>=0 for x in nonneg):
        raise ValueError('passive model needs positive storage and nonnegative losses')
    if not all(isfinite(x) for x in (p.exogenous_dc,p.exogenous_ac)):
        raise ValueError('finite source')

def exogenous(t,p):
    # Exogenous waveform delayed, not a validated Sun-to-collector Green function.
    return p.exogenous_dc+p.exogenous_ac*sin(2*pi*p.exogenous_freq*max(0.,t-p.delay))

def state_size(p):return 1+p.nodes+(p.nodes-1)+1

def unpack(y,p):
    N=p.nodes
    return y[0], y[1:1+N], y[1+N:2*N], y[2*N]

def powers_and_derivative(t,y,p):
    vs,v,i,n=unpack(y,p)
    if n < -1e-9:raise ValueError('negative carrier density')
    n=max(0.,n)
    vexo=exogenous(t,p)
    recharge=p.g_recharge*(vexo-vs)
    feed=p.g_feed*(vs-v[0])
    dv=np.empty(p.nodes)
    for k in range(p.nodes):
        inbound=feed if k==0 else i[k-1]
        outbound=0. if k==p.nodes-1 else i[k]
        dissipative=(p.g_load*v[k] if k==p.nodes-1 else 0.)
        if p.plasma_mode=='shunt' and k==p.plasma_node:dissipative+=p.g_plasma_per_n*n*v[k]
        dv[k]=(inbound-outbound-dissipative)/p.c_node
    gch=p.g_plasma_per_n*n
    channel_R=(1/gch if gch>0 else 1e30)
    link_R=np.full(p.nodes-1,p.r_link)
    if p.plasma_mode=='series':link_R[p.plasma_node]+=channel_R
    di=(v[:-1]-v[1:]-link_R*i)/p.l_link
    created=p.ion_seed+p.ion_driven
    lost=p.attachment*n+p.recombination*n*n
    dn=created-lost
    source_dv=(recharge-feed)/p.c_source
    powers=np.array([
        vexo*recharge,
        p.g_recharge*(vexo-vs)**2,
        p.g_feed*(vs-v[0])**2,
        p.r_link*np.dot(i,i),
        (p.g_plasma_per_n*n*v[p.plasma_node]**2 if p.plasma_mode=='shunt'
         else channel_R*i[p.plasma_node]**2),
        p.g_load*v[-1]**2,
        p.pair_energy*created,
        p.pair_energy*lost,
        p.controller_aux,
        p.controller_aux],dtype=float)
    derivative=np.concatenate(([source_dv],dv,di,[dn]))
    return derivative,powers

def symbolic_telescoping_check(nodes=5):
    """Exact polynomial conservation for arbitrary finite chosen N.

    Source and ionization work are paid and losses are positive terms under
    nonnegative rates. This is a discrete chain, NOT a Maxwell PDE theorem.
    """
    import sympy as sp
    vs, ve, nn = sp.symbols("vs ve nn", real=True)
    vv=sp.symbols("v0:"+str(nodes), real=True)
    ii=sp.symbols("i0:"+str(nodes-1), real=True)
    cs, cn, ll, gr, gf, gl, rr, gp, pump, loss, aux=sp.symbols(
        "Cs Cn L gr gf gl R gp pump loss aux", real=True)
    recharge=gr*(ve-vs); feed=gf*(vs-vv[0])
    dvs=(recharge-feed)/cs
    dv=[]
    for k in range(nodes):
        incoming=feed if k==0 else ii[k-1]
        outgoing=0 if k==nodes-1 else ii[k]
        shunt=(gl*vv[k] if k==nodes-1 else 0)
        if k==nodes//2:shunt+=gp*nn*vv[k]
        dv.append((incoming-outgoing-shunt)/cn)
    di=[(vv[k]-vv[k+1]-rr*ii[k])/ll for k in range(nodes-1)]
    energy_rate=cs*vs*dvs+cn*sum(vv[k]*dv[k] for k in range(nodes))+ll*sum(ii[k]*di[k] for k in range(nodes-1))+pump-loss
    p_in=ve*recharge+pump+aux
    p_out=(gr*(ve-vs)**2+gf*(vs-vv[0])**2+rr*sum(x*x for x in ii)
          +gl*vv[-1]**2+gp*nn*vv[nodes//2]**2+loss+aux)
    assert sp.expand(p_in-p_out-energy_rate)==0
    # Series alternative inserts dissipative Rc in one link; account Rc*I_j^2.
    j=nodes//2-1
    Rc=sp.symbols('Rc',real=True)
    di_series=list(di)
    di_series[j]-=Rc*ii[j]/ll
    rate_series=(energy_rate+ll*ii[j]*(di_series[j]-di[j])).subs(gp,0)
    out_series=(p_out+Rc*ii[j]**2).subs(gp,0)
    return sp.expand(p_in-out_series-rate_series)==0

def energy(y,p):
    vs,v,i,n=unpack(y,p)
    return (p.c_source*vs*vs/2+p.c_node*np.dot(v,v)/2+
            p.l_link*np.dot(i,i)/2+p.pair_energy*n)

def instantaneous_residual(t,y,p):
    dy,w=powers_and_derivative(t,y,p)
    vs,v,i,n=unpack(y,p)
    dvs,dv,di,dn=unpack(dy,p)
    udot=p.c_source*vs*dvs+p.c_node*np.dot(v,dv)+p.l_link*np.dot(i,di)+p.pair_energy*dn
    return w[0]+w[6]+w[8]-sum(w[k] for k in (1,2,3,4,5,7,9))-udot

def run(p=Model(),duration=10.,sampling=200):
    validate(p)
    if duration<=0 or sampling<10:raise ValueError('invalid horizon')
    y0=np.concatenate(([0.],np.zeros(p.nodes),np.zeros(p.nodes-1),[p.n_init],np.zeros(len(ENERGY_KEYS))))
    sz=state_size(p)
    def rhs(t,y):
        dy,w=powers_and_derivative(t,y[:sz],p)
        return np.concatenate((dy,w))
    result=solve_ivp(rhs,(0,duration),y0,rtol=2e-9,atol=2e-11,
                     max_step=duration/sampling)
    if not result.success:raise ArithmeticError(result.message)
    end=result.y[:,-1]
    all_work=dict(zip(ENERGY_KEYS,map(float,end[sz:])))
    u0,u1=energy(y0[:sz],p),energy(end[:sz],p)
    in_work=all_work['upstream_input']+all_work['ion_creation_paid']+all_work['controller_input']
    out_work=sum(all_work[k] for k in ('recharge_heat','feed_heat','link_heat','plasma_heat','load','ion_loss','controller_loss'))
    residual=in_work-out_work-(u1-u0)
    point_residual=max(abs(instantaneous_residual(t,result.y[:sz,k],p)) for k,t in enumerate(result.t))
    return dict(scope='finite spatial LC/plasma analogue; no original source claim',
        params=p.__dict__, work=all_work, initial_energy=u0,final_energy=u1,
        energy_delta=u1-u0,net_balance_residual=residual,
        max_pointwise_residual=point_residual,
        natural_energy_at_upstream=all_work['upstream_input'],
        net_useful_after_control_and_ionization=all_work['load']-all_work['ion_creation_paid']-all_work['controller_input'],
        storage_restored=bool(abs(u1-u0)<1e-6),
        physical_gate='P2/R2/R3 OPEN',
        final_density=float(end[2*p.nodes]),
        channel_conductance=float(p.g_plasma_per_n*end[2*p.nodes]))

if __name__=='__main__':
    baseline=run()
    changed=run(replace(Model(),ion_driven=0.8,controller_aux=0.02))
    print(json.dumps({'baseline':baseline,'controlled':changed},indent=2))
