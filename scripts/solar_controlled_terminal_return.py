"""Explicitly paid ideal local material return on the original event owner.

This is a different terminal actuator model, never a free field reset or
a physical cooling/removal claim. Every world uses the same policy.
Actuator duration, impedance and empirical efficiency remain external.
"""
import numpy as np
from solar_support_transition import support_transition
from solar_physical_causal import MASS,CHARGE

def local_return(field,pop,pool,theta,target_pop,target_pool,vol,cap,chem,kinetics,policy):
    x,n,p,t,n0,p0,V,C,E=map(lambda a:np.asarray(a,float),
        (field,pop,pool,theta,target_pop,target_pool,vol,cap,chem))
    cells=len(V)
    if n.shape!=n0.shape or n.shape!=(cells,3) or p.shape!=p0.shape or p.shape!=(cells,2) or t.shape!=C.shape or t.shape!=(cells,) or E.shape!=(3,) or x.ndim!=1 or len(x)<9*cells:
        raise ValueError('material return shape mismatch')
    if not all(np.isfinite(a).all() for a in (x,n,p,t,n0,p0,V,C,E)):
        raise ValueError('nonfinite material return')
    if any(np.any(a<0) for a in (n,p,t,n0,p0,E)) or np.any(V<=0) or np.any(C<=0):
        raise ValueError('invalid material store')
    if not all(np.allclose(a[:,0],a[:,1:].sum(axis=1),rtol=1e-12,atol=0) for a in (n,n0)):
        raise ValueError('charge-neutral targets required')
    if not np.allclose(n[:,1:]+p,n0[:,1:]+p0,rtol=1e-12,atol=0):
        raise ValueError('target inventory cannot be reached by local exchange')
    # Reverse-solve the unique componentwise minimum number of ion pair events.
    delta=n0[:,1:]-n[:,1:]
    a=np.maximum(delta,0.);r=np.maximum(-delta,0.)
    a=np.column_stack((a.sum(axis=1),a));r=np.column_stack((r.sum(axis=1),r))
    if np.any(r>n) or np.any(a[:,1:]>p+r[:,1:]):
        raise ValueError('insufficient local reservoir')
    removal=np.asarray(policy['removed_limit_m3'],float);creation=np.asarray(policy['created_limit_m3'],float)
    Q=C*t;cooling=np.asarray(policy['cooling_limit_J'],float);cop=np.asarray(policy['cooling_COP'],float)
    birth=np.asarray(policy['birth_velocity_m_s'],float)
    if removal.shape!=n.shape or creation.shape!=n.shape or cooling.shape!=t.shape or cop.shape!=t.shape or birth.shape!=(cells,3,3):
        raise ValueError('actuator policy shape mismatch')
    if not all(np.isfinite(v).all() for v in (removal,creation,cooling,cop,birth)) or np.any(removal<0) or np.any(creation<0) or np.any(cooling<0) or np.any(cop<=0):
        raise ValueError('invalid actuator bounds')
    if np.any(r>removal) or np.any(a>creation) or np.any(Q>cooling):
        raise ValueError('actuator capacity exceeded')
    eta=float(kinetics['chemical_input_efficiency']); er=float(kinetics['chemical_recovery_efficiency'])
    extra=float(policy['extra_actuator_work_J']);budget=float(policy['gross_paid_budget_J'])
    if not all(np.isfinite(v) for v in (eta,er,extra,budget)) or not 0<eta<=1 or not 0<=er<=1 or extra<0 or budget<0:
        raise ValueError('invalid actuator work terms')
    y=x.copy(); new=n.copy(); neutral=p+r[:,1:]-a[:,1:]
    k=np.zeros(3);receipts=[];offset=len(x)-9*cells
    for i in range(cells):
        sl=slice(offset+9*i,offset+9*i+9)
        y[sl],new[i],ledger,receipt=support_transition(x[sl],n[i],r[i],a[i],birth[i],V[i])
        k+=ledger;receipts.append(receipt)
    if not np.allclose(new,n0,rtol=1e-12,atol=0) or not np.allclose(neutral,p0,rtol=1e-12,atol=0):
        raise ArithmeticError('material return residual exceeds arithmetic allowance')
    formed=float(np.einsum('is,i,s->',a,V,E));removed=float(np.einsum('is,i,s->',r,V,E))
    cool_work=float(np.sum(Q/cop))
    gross=(formed+k[0])/eta+cool_work+extra; recovery=er*removed
    if gross>budget:raise ValueError('gross terminal actuator budget exceeded')
    # theta'=theta-Q/C=0 by definition of the metered extraction Q=C theta.
    # The field cochains are untouched, and current is changed only by event.
    thermal=np.zeros_like(t)
    def energy(z,d,T):return float(z@z/2+C@T+np.einsum('is,i,s->',d,V,E))
    before=energy(x,n,t);after=energy(y,new,thermal)
    balance=after-before+k[1]+k[2]+removed+float(Q.sum())-k[0]-formed
    if abs(balance)>1e-9*max(abs(before),abs(after),abs(formed),abs(removed),abs(float(Q.sum())),1e-30):
        raise ArithmeticError('controlled return work balance mismatch')
    return (y,new,neutral,thermal),dict(removed_m3=r.tolist(),created_m3=a.tolist(),
        cooling_extracted_J=Q.tolist(),cooling_work_J=cool_work,
        gross_paid_J=float(gross),chemical_recovery_J=recovery,net_paid_J=float(gross-recovery),
        kinetic_ledger_J=k.tolist(),formation_J=formed,recombination_J=removed,
        balance_J=float(balance),events=receipts,
        electromagnetic_cochains_unchanged=bool(np.array_equal(x[:offset],y[:offset])),
        exact_physical_return_admitted=False,physical_admission=False,
        scope='ideal local terminal event; actuator duration and physical parameters not admitted')

def controlled_terminal_cycle(material,cfg,policy):
    from solar_spherical_cycle import cycle,geometry
    if not cfg.get('fixed_horizon',True):
        raise ValueError('controlled comparison requires common fixed horizon')
    cc=dict(cfg,retain_history=True)
    base=cycle(material,cc)
    vol,_,ne,nf=geometry(cc['radii_m'],cc['angular_level'],int(cc.get('nested_depth',0)));n=len(vol);N=ne+nf+9*n
    last=np.asarray(base['history'][-1],float)
    x=last[:N];pop=last[N:N+3*n].reshape(n,3);pool=last[N+3*n:N+5*n].reshape(n,2);theta=last[N+5*n:]
    q=cc['kinetics'];pop0=np.asarray(material[2])*MASS/CHARGE**2;pool0=np.asarray(q['initial_neutral_m3'])
    cap=np.asarray(cc['heat_capacity_J_K']);chem=np.asarray(q['formation_J_per_particle'])
    end,w=local_return(x,pop,pool,theta,pop0,pool0,vol,cap,chem,q,policy)
    start=(np.zeros(N),pop0,pool0,np.zeros(n))
    tol=np.asarray(cc.get('return_atol',[1e-10]*4),float);rtol=float(cc['return_rtol'])
    residual=[float(np.linalg.norm(a-b)) for a,b in zip(end,start)]
    accepted=all(r<=t+rtol*np.linalg.norm(b) for r,t,b in zip(residual,tol,start))
    initial=float(np.einsum('is,i,s->',pop0,vol,chem))
    final=float(end[0]@end[0]/2+cap@end[3]+np.einsum('is,i,s->',end[1],vol,chem))
    depletion=max(0.,initial-final)
    net=base['campaign_net_J']-w['net_paid_J']-depletion-base['campaign_ledger']['balance_abs_J']-abs(w['balance_J'])
    if net>base['campaign_ledger']['incident_J']+1e-8*max(1.,abs(net)):
        raise ArithmeticError('controlled campaign exceeds incident work')
    return dict(original_prefix=base,controlled_return=w,return_residual=residual,
        controlled_tolerance_restored=bool(accepted),controlled_tolerance_net_J=float(net) if accepted else None,
        terminal_depletion_J=depletion,physical_admission=False,exact_full_return_admitted=False)

def controlled_four_worlds(material,cfg,policy):
    worlds={}
    for source in (False,True):
        for active in (False,True):
            cc=dict(cfg)
            if not source:cc['incident_sqrt_W']=np.zeros_like(cfg['incident_sqrt_W'])
            if not active:cc['heating_W']=np.zeros_like(cfg['heating_W'])
            name=('source' if source else 'off')+'_'+('active' if active else 'passive')
            try:worlds[name]=controlled_terminal_cycle(material,cc,policy)
            except (ValueError,AssertionError,ArithmeticError,np.linalg.LinAlgError) as exc:
                worlds[name]=dict(controlled_tolerance_net_J=None,rejected=str(exc))
    a,p,oa,op=[worlds[k]['controlled_tolerance_net_J'] for k in ('source_active','source_passive','off_active','off_passive')]
    for v in (oa,op):
        if v is not None and v>1e-8*max(1.,abs(v)):
            raise ArithmeticError('source-off controlled gain contradicts paid ledger')
    return dict(worlds=worlds,selected_passive_advantage_J=None if a is None or p is None else a-p,
        controlled_interaction_J=None if any(v is None for v in (a,p,oa,op)) else (a-p)-(oa-op),
        strongest_passive_certified=False,physical_admission=False)
