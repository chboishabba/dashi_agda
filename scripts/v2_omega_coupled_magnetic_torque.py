#!/usr/bin/env python3
"""Two-winding coenergy torque / thermal budget max-cut (constructed model).

Linear angle-varying mutual inductance with angle-independent quartic
self saturation. This is a mathematical test of the magnetic/shaft hypothesis,
not a fitted magnetic map of the original V2. Recovery is not optimised.
"""
from dataclasses import dataclass, asdict
import math, json
import numpy as np

@dataclass(frozen=True)
class Model:
    rpm:float=2354.0
    poles:int=4
    mean_L:tuple=((.07,.012),(.012,.065))
    cos_L:tuple=((.009,.004),(.004,.008))
    sin_L:tuple=((0.,.003),(.003,0.))
    R:tuple=(.5,.5)
    dc_current:tuple=(2.,2.)
    beta:float=.00003
    current_limit:float=7.0
    voltage_limit:float=320.
    bus_eta:float=.95
    @property
    def omega(self):return 2*math.pi*self.rpm/60
    def arrays(self):
        L=np.array(self.mean_L,dtype=float); A=np.array(self.cos_L,dtype=float);B=np.array(self.sin_L,dtype=float)
        R=np.array(self.R,dtype=float);c=np.array(self.dc_current,dtype=float)
        if not all(M.shape==(2,2) and np.allclose(M,M.T) for M in (L,A,B)):raise ValueError('inductance matrices must be symmetric')
        if R.shape!=(2,) or c.shape!=(2,) or np.min(R)<=0 or self.beta<0:raise ValueError('invalid loss or saturation')
        if self.rpm<=0 or self.poles<=0 or not 0<self.bus_eta<=1:raise ValueError('invalid parameters')
        # Weyl eigenvalue bound for all angles and current at current-limit.
        if np.linalg.eigvalsh(L).min() <= np.linalg.norm(A,2)+np.linalg.norm(B,2)+3*self.beta*self.current_limit**2:
            raise ValueError('unverified positive incremental inductance')
        return L,A,B,R,c

def coefficient(model):
    _,A,B,R,c=model.arrays()
    f=A@c;g=-B@c
    S=float(np.dot(f,f/R)+np.dot(g,g/R))
    K=model.poles*model.omega*math.sqrt(2*S)/2
    return f,g,S,K

def optimum(model,ac_copper_budget):
    """Exactly optimal sinusoidal quadratures at fixed *AC copper loss*.

    Magnetic torque functional is linear in sin/cos coefficients. Constraints
    sum R_j(u_j²+v_j²)/2 <= B. Cauchy in resistance-weighted norm
    certifies the global optimum among all first-harmonic coefficient vectors.
    Not a globally optimal current waveform / converter.
    """
    if ac_copper_budget<0:raise ValueError('negative budget')
    _,_,_,R,c=model.arrays();f,g,S,K=coefficient(model)
    scale=math.sqrt(2*ac_copper_budget/S) if S else 0.
    u=scale*f/R;v=scale*g/R
    return evaluate(model,u,v,certificate_K=K,ac_copper_budget=ac_copper_budget)

def evaluate(model,u,v,certificate_K=None,ac_copper_budget=None,n=2048):
    L,A,B,R,c=model.arrays();u=np.asarray(u,dtype=float);v=np.asarray(v,dtype=float)
    if u.shape!=(2,) or v.shape!=(2,):raise ValueError('requires two windings')
    th=np.linspace(0,2*math.pi,n,endpoint=False)
    i=c[None,:]+np.sin(th[:,None])*u+np.cos(th[:,None])*v
    ip=np.cos(th[:,None])*u-np.sin(th[:,None])*v
    La=L[None,:,:]+np.cos(th[:,None,None])*A[None,:,:]+np.sin(th[:,None,None])*B[None,:,:]
    dLa=-np.sin(th[:,None,None])*A[None,:,:]+np.cos(th[:,None,None])*B[None,:,:]
    lam=np.einsum('nij,nj->ni',La,i)-model.beta*i**3
    dlam=np.einsum('nij,nj->ni',dLa,i)+np.einsum('nij,nj->ni',La,ip)-3*model.beta*i**2*ip
    volt=i*R[None,:]+model.poles*model.omega*dlam
    torque=.5*np.einsum('ni,nij,nj->n',i,dLa,i)*model.poles
    # <i^T L'(x) i> = c^T (-A u + B v), after parity of cubic terms.
    shaft=model.poles*model.omega*(float(c@A@u)-float(c@B@v))/2
    copper_dc=float(np.dot(R,c*c)); copper_ac=float(np.dot(R,(u*u+v*v)/2));copper=copper_dc+copper_ac
    terminal=float(np.mean(np.einsum('ni,ni->n',volt,i)))
    mean_torque=-float(np.mean(torque)); numerical_shaft=mean_torque*model.omega
    raw_bus=shaft-copper
    # Sufficient continuous envelope, using global bounds on derivatives of i and L.
    Iabs=np.abs(c)+np.abs(u)+np.abs(v)
    ipabs=np.abs(u)+np.abs(v)
    second_i=np.abs(u)+np.abs(v)
    L0_norm=np.linalg.norm(L,2)+np.linalg.norm(A,2)+np.linalg.norm(B,2)
    Lp_norm=np.linalg.norm(A,2)+np.linalg.norm(B,2)
    Vbound=float(np.max(R*Iabs)+model.poles*model.omega*(Lp_norm*np.linalg.norm(Iabs)+L0_norm*np.linalg.norm(ipabs)+3*model.beta*np.max(Iabs)**2*np.max(ipabs)))
    # Derivative Lipschitz bound of each winding's terminal voltage.
    Lpp_norm=Lp_norm
    dV_bound=(np.max(R*ipabs)+model.poles*model.omega*(Lpp_norm*np.linalg.norm(Iabs)+2*Lp_norm*np.linalg.norm(ipabs)+L0_norm*np.linalg.norm(second_i)+3*model.beta*(2*np.max(Iabs)*np.max(ipabs)**2+np.max(Iabs)**2*np.max(second_i))))
    grid_cert=float(np.max(np.abs(volt))+dV_bound*math.pi/n)
    f,g,S,K=coefficient(model)
    bound=K*math.sqrt(copper_ac)
    return {'u':u.tolist(),'v':v.tolist(),'shaft_w':shaft,'shaft_from_sampled_torque_w':numerical_shaft,
      'copper_dc_w':copper_dc,'copper_ac_w':copper_ac,'copper_total_w':copper,'raw_bus_w':raw_bus,'exported_bus_w':model.bus_eta*max(raw_bus,0),
      'terminal_port_mean_w':terminal,'energy_balance_residual_w':terminal+copper*0-shaft*(-1)-copper, # terminal = copper-shaft
      'mean_torque_nm':mean_torque,'peak_abs_current_a':float(np.max(np.abs(i))),
      'sampled_peak_voltage_v':float(np.max(np.abs(volt))),
      'continuous_voltage_sufficient_bound_v':Vbound,'grid_lipschitz_voltage_bound_v':grid_cert,
      'continuous_voltage_certified':Vbound<=model.voltage_limit,'grid_voltage_certified':grid_cert<=model.voltage_limit,
      'peak_current_sufficient_bound_a':float(np.max(Iabs)),'current_certified':float(np.max(Iabs))<=model.current_limit,
      'cauchy_shaft_upper_bound_w':bound,'optimality_slack_w':bound-shaft,
      'expected_optimal':certificate_K is not None,'budget_match_w':copper_ac-ac_copper_budget if ac_copper_budget is not None else None}

def matched_output(model,target_bus_w=20.):
    """Solve AC budget for fixed bus output on optimal coupled or decoupled family."""
    if target_bus_w<=0:raise ValueError('target must be positive')
    *_,K=coefficient(model)
    _,_,_,R,c=model.arrays()
    dc=float(np.dot(R,c*c)); target_raw=target_bus_w/model.bus_eta
    discr=K*K-4*(dc+target_raw)
    if discr<0:raise ValueError('target not achievable in this sinusoidal model')
    # stable lower positive root to avoid cancellation
    y=2*(dc+target_raw)/(K+math.sqrt(discr))
    result=optimum(model,y*y)
    assert abs(result['exported_bus_w']-target_bus_w)<1e-8
    return result

def variants():
    base=Model();L,A,B,R,c=base.arrays()
    from dataclasses import replace
    diag=replace(base,cos_L=tuple(map(tuple,np.diag(np.diag(A)))),sin_L=((0.,0.),(0.,0.)))
    cancel=replace(base,cos_L=((.009,-.004),(-.004,.008)),sin_L=((0.,-.003),(-.003,0.)))
    # These are distinct physical geometry hypotheses; do not imply switching changes material!
    out={}
    for name,m in [('coupled',base),('uncoupled',diag),('opposing_mutual',cancel)]:
        q=matched_output(m)
        out[name]={'model':asdict(m),'matched_output':q,'same_common_speed_and_resistance':True}
    return out

def run():
    m=Model();b=.25; optim=optimum(m,b)
    alt=evaluate(m,[optim['u'][0],-optim['u'][1]],optim['v'])
    return {'schema':'DASHI.V2.magnetic-coupling-geometry.v1','one_budget_optimum':optim,
      'phase_flip_negative_control':alt,'matched_bus_variants':variants(),
      'strong_gates':{'source_magnetic_map':'OPEN','full_core_hysteresis':'OPEN','real_current_tracking':'OPEN','original_v2_load_interventions':'OPEN','agda_kernel':'NOT RUN'},
      'not_a_v2_measurement':True}

def matched_control_direction(model, u_direction, v_direction, target_bus_w=20.):
    """Match bus output using a fixed current-phasing direction in SAME machine.

    Uses the lower AC copper root; no adjustment of geometry, RPM, recovery,
    baseline current, or material parameters.
    """
    _,A,B,R,c=model.arrays();u=np.asarray(u_direction,float);v=np.asarray(v_direction,float)
    norm=float(np.dot(R,u*u+v*v)/2)
    if norm<=0:raise ValueError('zero modulation direction')
    u/=math.sqrt(norm);v/=math.sqrt(norm)
    geom=model.poles*model.omega*(float(c@A@u)-float(c@B@v))/2
    dc=float(np.dot(R,c*c));required=dc+target_bus_w/model.bus_eta
    if geom<=0 or geom**2<4*required:raise ValueError('direction does not support target')
    y=2*required/(geom+math.sqrt(geom**2-4*required))
    q=evaluate(model,y*u,y*v)
    assert abs(q['exported_bus_w']-target_bus_w)<1e-8
    return q

def same_geometry_control_comparison(model=Model(),target_bus_w=20.):
    """Coupled-optimal vs controller ignoring coupling on SAME magnetic geometry."""
    _,A,B,R,c=model.arrays();f,g,_,_=coefficient(model)
    ideal=matched_output(model,target_bus_w)
    uncoupled_dir=np.diag(np.diag(A))@c/R
    # Do not use B mutual cross path when designing the uncoupled controller.
    naive=matched_control_direction(model,uncoupled_dir,[0,0],target_bus_w)
    return {'same_geometry':True,'same_copper_material_and_resistance':True,
        'optimal_joint':ideal,'uncoupled_designed_timing':naive,
        'shaft_saving_w':naive['shaft_w']-ideal['shaft_w'],
        'copper_saving_w':naive['copper_total_w']-ideal['copper_total_w'],
        'same_target_export_w':target_bus_w,
        'claim':'within the same two-winding model, coordinated phasing reduces shaft/copper cost at equal exported watts'}

if __name__=='__main__':
    result=run()
    result['same_geometry_control_comparison']=same_geometry_control_comparison()
    print(json.dumps(result,indent=2))
