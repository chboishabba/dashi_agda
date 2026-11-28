"""Same-state cochain thermal/chemical cycle and matched four-world comparison.
Graph incidences are barycentric support links, not measured physical faces.
Uses diagonal Hodge candidate; full consistent mass remains reference.
"""
import numpy as np
from scipy.constants import c
from solar_spherical_material_weld import construct,structural_stage_atlas,assembly_mesh
from solar_matrix_storage import diagonal
from scipy.sparse import csr_matrix
from solar_population_event import reaction,MASS,CHARGE
from solar_support_transition import support_transition
from solar_restoration_geometry import thermal_return_geometry,analytic_support_return_obstruction
from solar_asymptotic_return import source_off_tail_receipt
from solar_population_amplitude_event import right_reaction_support
from solar_earth_collision_tensor import rates
from solar_physical_cone import timed_step

from solar_spherical_geometry import geometry

def cycle(material,cfg,shadow=None):
    rows,neutral,D,gyro,axis=material
    depth=int(cfg.get('nested_depth',0)); sparse=bool(depth or cfg.get('sparse_operator',False))
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'],depth); n=len(vol)
    # One original row and provenance key per tetrahedron, explicitly assigned.
    assert len(rows)==n and len(cfg['row_keys'])==n
    D=np.asarray(D,float); pop0=D*MASS/CHARGE**2
    assert np.all(pop0>=0) and np.allclose(pop0[:,0],pop0[:,1:].sum(axis=1),rtol=1e-9,atol=1e-20)
    q=cfg['kinetics']; pool0=np.asarray(q['initial_neutral_m3'],float)
    chem=np.asarray(q['formation_J_per_particle'],float); birth=np.asarray(q['birth_velocity_m_s'],float)
    cap=np.asarray(cfg['heat_capacity_J_K'],float); cool=np.asarray(cfg['cooling_W_K'],float)
    assert pool0.shape==(n,2) and np.all(pool0>=0) and chem.shape==(3,) and np.all(chem>=0)
    assert birth.shape==(n,3,3) and cap.shape==cool.shape==(n,) and np.all(cap>0) and np.all(cool>0)
    src=np.asarray(cfg['incident_sqrt_W'],float); heat=np.asarray(cfg['heating_W'],float)
    assert len(src)>0 and heat.shape==(len(src),n) and np.all(heat>=0)
    dt=cfg['period_s']/len(src); assert dt>0
    size=ne+nf+9*n; x=np.zeros(size); pop=pop0.copy(); pool=pool0.copy(); theta=np.zeros(n)
    port=np.zeros(size); edge=int(cfg['source_edge']); assert 0<=edge<ne
    port[edge]=cfg['source_coupling_sqrt_inv_s']; assert port[edge]>0
    load=np.zeros(size); load[:ne]=cfg['load_rate_s_inv']; assert np.all(load>=0)
    L=diagonal(load,sparse); S=diagonal(port**2,sparse)
    def energy():
        return x@x/2+cap@theta+np.einsum('is,i,s->',pop,vol,chem)
    original=(x.copy(),pop.copy(),pool.copy(),theta.copy())
    analytic_pop_support=pop0>0;analytic_pool_support=pool0>0
    def residual(a,b):
        return [float(np.linalg.norm(u-v)/max(np.linalg.norm(u),np.linalg.norm(v),1e-30)) for u,v in zip(a,b)]
    assert int(cfg['max_cycles'])>=1 and cfg['auxiliary_J']>=0
    assert 0<cfg['heater_efficiency']<=1 and 0<q['chemical_input_efficiency']<=1 and 0<=q['chemical_recovery_efficiency']<=1
    campaign={}; preparation={}; trace=[]; history=[]; sensitivity=[]; support_receipts=[]
    from fractions import Fraction
    solve_error=Fraction(0); event_error_exact=Fraction(0)
    exact_trace=cfg.get('retain_stage_residuals',False)
    exact_events=bool(cfg.get('retain_nonfrozen_event_residuals',False))
    if exact_events and not exact_trace:raise ValueError('nonfrozen event enclosure requires exact stage residuals')
    if exact_events:
        from solar_event_rounding import event_rounding_receipt
    if exact_trace and not exact_events and (np.any(q['recombination_m3_s']) or np.any(q['ionization_s_inv']) or np.any(q['heater_ionization_per_J'])):
        raise ValueError('exact campaign solve enclosure requires frozen population or explicit binary event enclosure')
    retain_sensitivity=bool(cfg.get('retain_sensitivity',False) or exact_trace)
    initial_energy=energy()
    tail=int(cfg.get('restoration_steps',0)); assert tail>=0
    horizon=int(cfg['max_cycles'])
    # All worlds use identical source-off terminal slots; no external reset.
    terminal_load=np.asarray(cfg.get('terminal_load_rate_s_inv',load[:ne]),float)
    assert terminal_load.shape==(ne,) and np.all(terminal_load>=0)
    terminal_L=diagonal(np.r_[terminal_load,np.zeros(size-ne)],sparse)
    atol=np.asarray(cfg.get('return_atol',[1e-10,1e-10,1e-10,1e-10]),float)
    assert atol.shape==(4,) and np.all(atol>=0)
    atlas=None; residual_trace=[]; residual_bound=0.; work_error_bound=0.;step_index=0
    if shadow is not None:
        from solar_evolution_residual import event_affine,residual_step
        P=shadow['prolongation']; reference=np.asarray(shadow['endpoints'],float)
        reference_work=np.asarray(shadow['useful_J'],float)
        if not cfg.get('fixed_horizon',True) or reference.shape!=(horizon*len(src)+tail,P.shape[1]) or P.shape[0]!=size or reference_work.shape!=(len(reference),):
            raise ValueError('shadow requires same fixed physical endpoint clock')
    for iteration in range(int(cfg['max_cycles'])):
        initial=(x.copy(),pop.copy(),pool.copy(),theta.copy()); total={}
        steps=list(zip(src,heat))
        if iteration==horizon-1: steps += [(0.,np.zeros(n)) for _ in range(tail)]
        for step,(inc,p) in enumerate(steps):
            terminal=step>=len(src)
            current_L=terminal_L if terminal else L
            before=energy(); costs=np.zeros(5)
            if shadow is not None:
                shadow_x=np.zeros(size) if step_index==0 else np.asarray(P@reference[step_index-1]).ravel()
            for i in range(n):
                analytic_pop_support[i],analytic_pool_support[i]=right_reaction_support(
                    analytic_pop_support[i],analytic_pool_support[i],p[i],0.,q)
                r,a,pool[i]=reaction(pop[i],pool[i],rows[i]['te']+theta[i],p[i],dt,q)
                sl=slice(ne+nf+9*i,ne+nf+9*i+9)
                if shadow is not None and (not exact_trace or exact_events):
                    coef,shift=event_affine(pop[i],r,a,birth[i],vol[i],MASS,CHARGE)
                    shadow_x[sl]=coef*shadow_x[sl]+shift
                if exact_trace and not exact_events:
                    # Rates are admitted only on the frozen-population chart.
                    # Avoid a numerically rounded current -> velocity -> current
                    # conversion when its exact mathematical action is identity.
                    if np.any(r) or np.any(a):
                        raise ValueError('frozen-population certificate encountered nonzero event')
                    w=np.zeros(3)
                else:
                    if exact_events:old_z=x[sl].copy();old_n=pop[i].copy()
                    x[sl],pop[i],w,support_receipt=support_transition(
                        x[sl],pop[i],r,a,birth[i],vol[i])
                    if exact_events:
                        er=event_rounding_receipt(old_z,old_n,r,a,birth[i],vol[i],MASS,CHARGE,x[sl])
                        local_error=Fraction(er['error_l1_exact']);solve_error+=local_error;event_error_exact+=local_error
                    if support_receipt['support_changed']:
                        support_receipts.append(dict(cycle=iteration+1,step=step,
                                                     cell=i,receipt=support_receipt))
                costs[:3]+=w; costs[3]+=vol[i]*(a@chem); costs[4]+=vol[i]*(r@chem)
            theta1=np.exp(-dt*cool/cap)*theta-np.expm1(-dt*cool/cap)*p/cool
            mid=np.exp(-dt*cool/(2*cap))*theta-np.expm1(-dt*cool/(2*cap))*p/cool
            absorbed=dt*p.sum(); bath=absorbed-cap@(theta1-theta); theta=theta1
            nu=rates([dict(r,te=r['te']+mid[i]) for i,r in enumerate(rows)],neutral)
            model=construct(cfg['radii_m'],cfg['angular_level'],np.arange(n),vol,pop*CHARGE**2/MASS,nu,gyro,axis,nested_depth=depth,sparse_operator=sparse)
            if cfg.get('common_stage_atlas',False) and atlas is None:
                atlas=structural_stage_atlas(model,mesh)
            A=model['generator']-current_L-S
            x,w=timed_step(x,A,2*inc*port,dt,mesh,dict(collision=model['loss'],load=current_L,source=S),port,inc,retain_local_midpoint=retain_sensitivity,retain_stage_residuals=exact_trace,atlas_pairs=atlas,exact_port_base=model['generator'] if exact_trace else None)
            if retain_sensitivity:
                item=dict(terminal=terminal,edge_midpoint=w['local_midpoint'][:ne],reflected=w['reflected_amplitude'],incident=float(inc),useful_J=w['loss_channels_J']['load'])
                if exact_trace:
                    item['midpoint_error']=[str(solve_error+Fraction(v)) for v in w['exact_binary_midpoint_error'][:ne]]
                    solve_error+=Fraction(w['exact_binary_stage_error'])
                    item['state_error']=str(solve_error)
                sensitivity.append(item)
            channels=w['loss_channels_J']; useful=channels['load']; collision=channels['collision']
            if shadow is not None:
                sy,sr=timed_step(shadow_x,A,2*inc*port,dt,mesh,retain_local_midpoint=True,atlas_pairs=atlas)
                er=residual_step(x,sy,np.asarray(P@reference[step_index]).ravel(),residual_bound,
                    sr['local_midpoint'],current_L.diagonal(),dt,reference_work[step_index],useful)
                residual_bound=er['error_bound_candidate'];work_error_bound+=er['work_error_bound_candidate_J']
                er['time']=[iteration,step]; residual_trace.append(er)
            step_index+=1
            paid=absorbed/cfg['heater_efficiency']+(costs[0]+costs[3])/q['chemical_input_efficiency']-q['chemical_recovery_efficiency']*costs[4]
            balance=energy()-before+w['outgoing_J']+useful+collision+bath+costs[1]+costs[2]+costs[4]-w['incident_J']-absorbed-costs[0]-costs[3]
            assert abs(balance)<=1e-8*max(abs(before),abs(energy()),w['incident_J'],absorbed,costs[3],1e-30)
            if cfg.get('retain_history',False): history.append(np.r_[x,pop.ravel(),pool.ravel(),theta].tolist())
            for k,v in dict(useful_J=useful,paid_J=paid,incident_J=w['incident_J'],outgoing_J=w['outgoing_J'],collision_J=collision,balance_abs_J=abs(balance)).items():
                total[k]=total.get(k,0.)+float(v)
        end=(x,pop,pool,theta); ret=residual(end,initial)
        for key,value in total.items(): campaign[key]=campaign.get(key,0.)+value
        trace.append(dict(cycle=iteration+1,return_residual=ret,ledger=dict(total)))
        if not cfg.get('fixed_horizon',True) and tail==0 and max(ret)<=cfg['return_rtol']:break
        if iteration+1<int(cfg['max_cycles']):
            for key,value in total.items(): preparation[key]=preparation.get(key,0.)+value
    # Periodic orbit and original reservoir return are separate obligations.
    orig=residual(end,original); restored=max(ret)<=cfg['return_rtol']
    material_restored=max(orig[1:])<=cfg['return_rtol']
    net=total['useful_J']-total['paid_J']-cfg['auxiliary_J']
    # Preparation is charged gross (no credit for its useful output); auxiliary per cycle.
    prep_paid=max(0.,preparation.get('paid_J',0.))+iteration*cfg['auxiliary_J']
    campaign_net=campaign['useful_J']-campaign['paid_J']-(iteration+1)*cfg['auxiliary_J']
    full_restored=all(np.linalg.norm(a-b)<=tol+cfg['return_rtol']*np.linalg.norm(b) for a,b,tol in zip(end,original,atol))
    # No credit for depletion even inside accepted restoration tolerances.
    depletion=max(0.,float(initial_energy-energy()))
    corrected_net=campaign_net-depletion-campaign['balance_abs_J']
    assert corrected_net<=campaign['incident_J']+1e-8*max(1.,campaign['incident_J'])
    thermal_geometry=thermal_return_geometry(heat,dt,cap,cool,iteration+1,tail,atol[3])
    support_geometry=analytic_support_return_obstruction(pop0>0,analytic_pop_support)
    tail_receipt=None
    if 'asymptotic_tail_probe_steps' in cfg:
        tail_receipt=source_off_tail_receipt(x,pop,pool,theta,pop0,pool0,vol,chem,cap,cool,q,dt,cfg['asymptotic_tail_probe_steps'])
        tail_receipt['prefix_campaign_net_J']=campaign_net
        if 'work' in tail_receipt:
            tail_receipt['conditional_limit_net_interval_J']=[campaign_net,campaign_net+tail_receipt['work']['additional_net_upper_J']]
            tail_receipt['interval_is_rounding_certified']=False
            from solar_changing_tail import tail_envelope
            tail_receipt['changing_operator_envelope']=tail_envelope(model,pop,theta,vol,rows,neutral,MASS,CHARGE,
                q['recombination_m3_s'],cap,cool,dt,cfg['asymptotic_tail_probe_steps'])
            tail_receipt['changing_operator_envelope']['requires_fixed_terminal_atlas']=True
    return dict(ledger=total,campaign_ledger=campaign,preparation_ledger=preparation,preparation_cost_J=prep_paid,
                asymptotic_tail=tail_receipt,
                analytic_return_geometry=dict(thermal=thermal_geometry,population=support_geometry,
                    exact_original_return_obstructed=thermal_geometry['exact_zero_return_obstructed'] or support_geometry['exact_zero_population_return_obstructed'],
                    current_strict_gate_is_tolerance_based=True),
                campaign_net_J=campaign_net,full_original_restored=bool(full_restored),
                strict_campaign_net_J=corrected_net if full_restored else None,
                terminal_depletion_J=depletion,
                nested_depth=depth,sparse_operator=sparse,
                signed_evolution_residual_trace=residual_trace,
                final_state_error_bound_candidate=residual_bound if shadow is not None else None,
                total_receiver_work_error_bound_candidate_J=work_error_bound if shadow is not None else None,
                common_stage_atlas=atlas is not None,
                support_transition_count=len(support_receipts),
                support_transition_receipts=support_receipts,
                fixed_support_campaign=not bool(support_receipts),
                exact_frozen_population_solve_error=str(solve_error) if exact_trace and not exact_events else None,
                exact_binary_field_solve_error=str(solve_error) if exact_trace else None,
                exact_binary_event_error=str(event_error_exact) if exact_events else None,
                fixed_binary_material_history_enclosure=bool(exact_trace),physical_material_rounding_enclosed=False,
                history=history,sensitivity_trace=sensitivity,elapsed_s=((iteration+1)*len(src)+tail)*dt,
                preparation_charged_periodic_net_J=net-prep_paid if restored and material_restored else None,
                cycle_trace=trace,net_J=net,periodic_return=ret,original_return=orig,
                restored=bool(restored),original_material_restored=bool(material_restored),
                physical_admission=False,conditional_net_J=net if restored and material_restored else None)

def four_worlds(material,cfg):
    worlds={}
    for source in (False,True):
        for active in (False,True):
            cc=dict(cfg)
            if not source:cc['incident_sqrt_W']=np.zeros_like(cfg['incident_sqrt_W'])
            if not active:cc['heating_W']=np.zeros_like(cfg['heating_W'])
            worlds['%s_%s'%('source' if source else 'off','active' if active else 'passive')]=cycle(material,cc)
    a=worlds['source_active']['strict_campaign_net_J']
    p=worlds['source_passive']['strict_campaign_net_J']
    oa=worlds['off_active']['strict_campaign_net_J']
    op=worlds['off_passive']['strict_campaign_net_J']
    # Strict original-state restoration is required for every term in the
    # source-specific interaction. An unrestored off-world is not silently
    # replaced by a conditional, depletion-adjusted or sampled value.
    interaction=None if any(z is None for z in (a,p,oa,op)) else (a-p)-(oa-op)
    # Off-source, the net external incident work is zero. A genuinely
    # restored source-off campaign cannot create useful net work from
    # activation already charged to the same resource ledger.
    for name in ('off_active','off_passive'):
        z=worlds[name]['strict_campaign_net_J']
        if z is not None and z>1e-8*max(1.,abs(worlds[name]['campaign_ledger']['paid_J'])):
            raise ArithmeticError('source-off restored gain contradicts paid-energy ledger')
    return dict(worlds=worlds,
                selected_passive_advantage_J=None if a is None or p is None else a-p,
                strict_source_interaction_J=interaction,
                source_interaction_admitted=interaction is not None,
                source_specific_causal_identification=False,
                strongest_passive_certified=False,physical_admission=False)
