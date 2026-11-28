"""Fixed-support spherical campaign Jacobian-vector product, original owners.
Actual reaction/event, thermal, collision, reciprocal Whitney and indexed Cayley
steps are reused. This is a smooth-chart derivative, not an optimum certificate.
"""
import numpy as np
from solar_matrix_storage import diagonal
from solar_physical_causal import MASS,CHARGE
from solar_spherical_cycle import geometry
from solar_spherical_material_weld import construct,structural_stage_atlas
from solar_thermal_population_tangent import reaction_jvp,event_jvp,thermal_jvp,collision_jvp
from solar_material_generator_jvp import material_jvp,amplitude_material_boundary_jvp,amplitude_exchange_jvp
from solar_quadratic_jet import reaction_u2,amplitude2,event_state2,work2,squared_return2
from solar_population_amplitude_event import event_amplitude_jvp,right_reaction_support
from solar_physical_cone import timed_step

def campaign_jvp(material,cfg,dheating,dload,quadratic_amplitude_path=False,quadratic_second_order=False,shadow=None):
    """Smooth chart, or one-sided s>=0 path with controls affine in u=s*s.
    In the latter chart density and thermal derivatives are retained in u,
    normalized current and the objective first derivative are in s.
    This is not a density-gradient or unrestricted optimization certificate.
    """
    rows,neutral,D,gyro,axis=material
    depth=int(cfg.get('nested_depth',0)); sparse=bool(depth or cfg.get('sparse_operator',False))
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'],depth); n=len(vol)
    assert len(rows)==n and len(cfg['row_keys'])==n
    src=np.asarray(cfg['incident_sqrt_W'],float)
    heat=np.asarray(cfg['heating_W'],float)
    dheat=np.asarray(dheating,float)
    load=np.asarray(cfg['load_rate_s_inv'],float)
    dload=np.asarray(dload,float)
    assert heat.shape==dheat.shape==(len(src),n)
    assert load.shape==dload.shape==(ne,)
    assert np.all(heat>=0) and np.all(load>=0)
    dt=cfg['period_s']/len(src); horizon=int(cfg['max_cycles'])
    q=cfg['kinetics']; chem=np.asarray(q['formation_J_per_particle'],float)
    birth=np.asarray(q['birth_velocity_m_s'],float)
    cap=np.asarray(cfg['heat_capacity_J_K'],float)
    cool=np.asarray(cfg['cooling_W_K'],float)
    pop=np.asarray(D,float)*MASS/CHARGE**2
    if not quadratic_amplitude_path and not np.all(pop>0):raise ValueError('positive population support chart required')
    if quadratic_amplitude_path and (not cfg.get('common_stage_atlas',False) or not cfg.get('fixed_horizon',True)):
        raise ValueError('quadratic path requires common atlas and fixed horizon')
    if quadratic_amplitude_path and (np.any((heat==0)&(dheat<0)) or np.any((load==0)&(dload<0))):
        raise ValueError('negative right control path')
    pool=np.asarray(q['initial_neutral_m3'],float).copy()
    theta=np.zeros(n);x=np.zeros(ne+nf+9*n)
    pop_right=pop>0; pool_right=pool>0
    if quadratic_second_order and not quadratic_amplitude_path:
        raise ValueError('second coefficient requires quadratic amplitude path')
    indexed_events=[]; paid_u=0.; useful2=0.; transport_receipts=[]
    dpop=np.zeros_like(pop);dpool=np.zeros_like(pool)
    dtheta=np.zeros_like(theta);dx=np.zeros_like(x)
    pop2=np.zeros_like(pop);pool2=np.zeros_like(pool);x2=np.zeros_like(x)
    elapsed=0.; arrival_history=np.full((3,len(x)),np.inf); ledger2=[]
    def energy2():
        return float(x@x2+dx@dx/2+cap@dtheta+np.einsum('is,i,s->',dpop,vol,chem))
    start=(x.copy(),pop.copy(),pool.copy(),theta.copy())
    dstart=(dx.copy(),dpop.copy(),dpool.copy(),dtheta.copy())
    port=np.zeros(len(x));port[int(cfg['source_edge'])]=float(cfg['source_coupling_sqrt_inv_s'])
    source=diagonal(port**2,sparse)
    paid=dpaid=useful=duseful=0.
    term_load=np.asarray(cfg.get('terminal_load_rate_s_inv',load),float)
    term_dload=np.zeros(ne) if 'terminal_load_rate_s_inv' in cfg else dload
    tail=int(cfg.get('restoration_steps',0))
    atlas=None; jet_residuals=[]; jet_radius=np.zeros(3); work_radius=np.zeros(3); shadow_index=0
    if shadow is not None:
        from solar_jet_error import event_difference_coefficients,event_difference,event_error,residual_coefficients,receiver_error
        if not quadratic_second_order:raise ValueError('shadow requires two-jet campaign')
        P=shadow['prolongation']; reference=np.asarray(shadow['endpoints'],float)
        reference_work=np.asarray(shadow['useful_coefficients_J'],float)
        if reference.shape!=(horizon*len(src)+tail,3,P.shape[1]) or P.shape[0]!=len(x) or reference_work.shape!=(len(reference),3):
            raise ValueError('unaligned coarse/fine coefficient clock')
        def lift(v):return np.asarray((P@v.T).T)
    for cycle_index in range(horizon):
        for index in range(len(src)+(tail if cycle_index==horizon-1 else 0)):
            terminal=index>=len(src)
            power=np.zeros(n) if terminal else heat[index]
            dpower=np.zeros(n) if terminal else dheat[index]
            inc=0. if terminal else src[index]
            cur_load=term_load if terminal else load
            cur_dload=term_dload if terminal else dload
            before2=energy2() if quadratic_second_order else 0.
            event_kinetic2=np.zeros(3)
            if shadow is not None:
                sx=np.zeros((3,len(x))) if shadow_index==0 else lift(reference[shadow_index-1])
                event_c1=event_c2=0.
            formed=removed_energy=birth_energy=0.
            dformed=dremoved_energy=dbirth_energy=0.
            for i in range(n):
                old=pop[i].copy();oldd=dpop[i].copy()
                primal,deriv=reaction_jvp(old,pool[i],rows[i]['te']+theta[i],
                    power[i],dt,q,oldd,dpool[i],dtheta[i],dpower[i])
                if quadratic_second_order:
                    r2,a2,pp2=reaction_u2(old,pool[i],rows[i]['te']+theta[i],power[i],dt,q,
                        oldd,dpool[i],dtheta[i],dpower[i],pop2[i],pool2[i])
                removed,created,newpool=primal
                dr,da,dnewpool=deriv
                sl=slice(ne+nf+9*i,ne+nf+9*i+9)
                if quadratic_amplitude_path:
                    pr,rr=right_reaction_support(pop_right[i],pool_right[i],power[i],dpower[i],q)
                    (z,pnew,kinetics),lift=event_amplitude_jvp(
                        x[sl],old,removed,created,birth[i],vol[i],
                        dx[sl],oldd,dr,da,pop_right[i],pr)
                    dz,dpnew=lift['state_jvp'],lift['population_u']
                    if quadratic_second_order:
                        z2,k2=event_state2(x[sl],dx[sl],x2[sl],old,removed,created,
                            oldd,dr,da,pop2[i],r2,a2,birth[i],np.sign(CHARGE)*np.sqrt(vol[i]*MASS),return_kinetic=True)
                        terms=np.array([z@z2,-x[sl]@x2[sl],dz@dz/2,-dx[sl]@dx[sl]/2,-k2[0],k2[1],k2[2]])
                        if abs(terms.sum())>1e-9*max(1e-30,np.sum(abs(terms))):
                            raise ArithmeticError('second coefficient event energy mismatch')
                        event_kinetic2+=k2
                        if shadow is not None:
                            coeff,oo,no=event_difference_coefficients(np.stack([old,oldd,pop2[i]]),np.stack([removed,dr,r2]),np.stack([created,da,a2]))
                            delta=sx[:,sl]-np.stack([x[sl],dx[sl],x2[sl]])
                            sx[:,sl]=np.stack([z,dz,z2])+event_difference(coeff,oo,no,delta)
                            event_c1=max(event_c1,float(np.max(abs(coeff[1]))));event_c2=max(event_c2,float(np.max(abs(coeff[2]))))
                        # Each event is local on the original cell. Newly reached
                        # coefficients require an inherited coordinate or actual
                        # nonzero birth momentum in the relevant order.
                        root_masks=[(created>0),(pnew==0)&(da>0),
                                    (created>0)|(da!=0)|(a2!=0)]
                        root_tags=[]
                        for order,state in enumerate((z,dz,z2)):
                            mask=(np.asarray(state)!=0)&~np.isfinite(arrival_history[order,sl])
                            for loc in np.flatnonzero(mask):
                                inherited=bool(np.any(np.isfinite(arrival_history[:order,sl][:,loc])))
                                born=bool(root_masks[order][loc//3] and birth[i,loc//3,loc%3]!=0)
                                if not (inherited or born):
                                    raise ValueError('unlicensed local event current coefficient')
                                arrival_history[order,sl][loc]=elapsed
                                root_tags.append(dict(order=order,coordinate=int(sl.start+loc),
                                    kind='local_birth_momentum' if born else 'local_inherited_coefficient'))
                        q2_before=amplitude2(old,oldd,pop2[i])
                        pop2[i]=pop2[i]-r2+a2;pool2[i]=pp2;x2[sl]=z2
                        q2_residual=amplitude2(pnew,dpnew,pop2[i])-q2_before
                    # Store actual signed residuals, independently of index labels.
                    indexed_events.append(dict(
                        index=dict(history=cfg['row_keys'][i],time=[cycle_index,index],
                            depth=dict(spatial=cfg['angular_level'],nested=depth,temporal=cfg.get('temporal_depth')),
                            iteration=cfg.get('frobenius_iteration'),
                            version=cfg.get('source_version','unversioned')),
                        cell=i,old_right=pop_right[i].tolist(),new_right=pr.tolist(),
                        signed_amplitude_residual=lift['signed_amplitude_residual'].tolist(),
                        signed_tangent_residual=lift['signed_tangent_residual'].tolist()))
                    if quadratic_second_order:
                        indexed_events[-1]['signed_coefficient2_residual']=q2_residual.tolist()
                        indexed_events[-1]['reach_roots']=root_tags
                    pop_right[i]=pr;pool_right[i]=rr
                else:
                    (z,pnew,kinetics),(dz,dpnew)=event_jvp(
                        x[sl],old,removed,created,birth[i],vol[i],
                        dx[sl],oldd,dr,da)
                x[sl]=z;dx[sl]=dz;pop[i]=pnew;dpop[i]=dpnew
                pool[i]=newpool;dpool[i]=dnewpool
                formed+=vol[i]*float(created@chem)
                removed_energy+=vol[i]*float(removed@chem)
                dformed+=vol[i]*float(da@chem)
                dremoved_energy+=vol[i]*float(dr@chem)
                birth_energy+=kinetics[0]
                dbirth_energy+=.5*vol[i]*float(
                    (MASS*da)@np.sum(birth[i]**2,axis=1))
            theta0=theta.copy();dt0=dtheta.copy()
            theta,dtheta=thermal_jvp(theta,power,dt,cap,cool,dtheta,dpower)
            half=np.exp(-dt*cool/(2*cap))
            beta=-np.expm1(-dt*cool/(2*cap))/cool
            mid=half*theta0+beta*power
            dmid=half*dt0+beta*dpower
            newrows=[dict(r,te=r['te']+mid[i]) for i,r in enumerate(rows)]
            nu,dnu=collision_jvp(newrows,neutral,dmid)
            Dcurrent=pop*CHARGE**2/MASS
            dD=dpop*CHARGE**2/MASS
            model=construct(cfg['radii_m'],cfg['angular_level'],np.arange(n),
                vol,Dcurrent,nu,gyro,axis,nested_depth=depth,sparse_operator=sparse)
            if cfg.get('common_stage_atlas',False) and atlas is None:
                atlas=structural_stage_atlas(model,mesh)
            if quadratic_amplitude_path:
                if np.any((Dcurrent==0)&(dD<0)):
                    raise ValueError('negative right density coefficient')
                dq=np.sqrt(np.where(Dcurrent==0,dD,0.))
                j=amplitude_material_boundary_jvp(model,vol,np.sqrt(Dcurrent),dq,nu,np.zeros_like(dnu),gyro,axis,pop_right)
            else:
                j=material_jvp(model,vol,Dcurrent,nu,dD,dnu)
            L=diagonal(np.r_[cur_load,np.zeros(len(x)-ne)],sparse)
            dL=diagonal(np.r_[np.zeros(ne) if quadratic_amplitude_path else cur_dload,np.zeros(len(x)-ne)],sparse)
            A=model['generator']-L-source
            dA=(j['d_right_generator'] if quadratic_amplitude_path else j['d_generator'])-dL
            right_limit=j['right_limit']-L-source if quadratic_amplitude_path else None
            jet2=None
            if quadratic_second_order:
                D2=pop2*CHARGE**2/MASS
                q2=amplitude2(Dcurrent,dD,D2)
                ex2=amplitude_exchange_jvp(model,vol,np.sqrt(Dcurrent),q2)['d_exchange']
                collision2_diag=np.zeros(len(x)); offset=len(x)-9*n
                for cell in range(n):
                    for species in range(3):
                        if pop_right[cell,species]:
                            ix=np.arange(offset+9*cell+3*species,offset+9*cell+3*species+3)
                            collision2_diag[ix]=dnu[cell,species]
                H2=ex2-diagonal(collision2_diag+np.r_[cur_dload,np.zeros(len(x)-ne)],sparse)
                jet2=(x2,H2,np.zeros_like(x))
            if shadow is not None:
                jet_radius=event_error(jet_radius,event_c1,event_c2)
                sy,sr=timed_step(sx[0],A,2*inc*port,dt,mesh,retain_local_midpoint=True,
                    jvp=(sx[1],dA,np.zeros_like(x)),atlas_pairs=atlas,right_limit=right_limit,
                    jet2=(sx[2],H2,np.zeros_like(x)),clock_start=elapsed,jet_error_seed=jet_radius)
            x,receipt=timed_step(x,A,2*inc*port,dt,mesh,
                dict(collision=model['loss'],load=L,source=source),port,inc,
                retain_local_midpoint=True,jvp=(dx,dA,np.zeros_like(x)),atlas_pairs=atlas,right_limit=right_limit,jet2=jet2,
                reach_seed=arrival_history if quadratic_second_order else None,
                clock_start=elapsed if quadratic_second_order else 0.)
            dx=np.asarray(receipt['state_jvp'],float)
            em=np.asarray(receipt['local_midpoint'][:ne],float)
            dem=np.asarray(receipt['local_midpoint_jvp'][:ne],float)
            if quadratic_second_order:
                x2=np.asarray(receipt['state_coefficient2'],float)
                em2=np.asarray(receipt['local_midpoint_coefficient2'][:ne],float)
                useful_step2=dt*work2(em,dem,em2,cur_load,cur_dload)
                useful2+=useful_step2
                work_coeff=np.array([dt*float(cur_load@em**2),2*dt*float((cur_load*em)@dem),useful_step2])
                if shadow is not None:
                    sj=np.stack([sy,sr['state_jvp'],sr['state_coefficient2']])
                    jres=residual_coefficients(np.stack([x,dx,x2]),sj,lift(reference[shadow_index]),sr['jet_endpoint_error_bound_candidate'])
                    jet_radius=np.asarray(jres['error_bound_candidate'])
                    sm=np.array([sr[k][:ne] for k in ('local_midpoint','local_midpoint_jvp','local_midpoint_coefficient2')])
                    sw=np.array([dt*float(cur_load@sm[0]**2),2*dt*float((cur_load*sm[0])@sm[1]),dt*work2(*sm,cur_load,cur_dload)])
                    wr=receiver_error(sm,sr['jet_local_midpoint_error_bound_candidate'],cur_load,cur_dload,dt)
                    if np.any(abs(work_coeff-sw)>wr+1e-10*np.maximum(1.,abs(work_coeff)+abs(sw))):raise ArithmeticError('coefficient midpoint work bound failed')
                    wr+=abs(sw-reference_work[shadow_index]);work_radius+=wr
                    jres.update(time=[cycle_index,index],receiver_work_error_bound_candidate_J=wr.tolist(),shadow_work_coefficients_J=sw.tolist())
                    jet_residuals.append(jres);shadow_index+=1
                m0=np.asarray(receipt['local_midpoint']);m1=np.asarray(receipt['local_midpoint_jvp'])
                m2=np.asarray(receipt['local_midpoint_coefficient2'])
                refl0=m0@port-inc;refl1=m1@port;refl2=m2@port
                outgoing2=dt*(refl1*refl1+2*refl0*refl2)
                collision2=dt*work2(m0,m1,m2,j['right_loss'].diagonal(),collision2_diag)
                absorbed2=dt*float(dpower.sum())
                bath2=absorbed2-cap@(dtheta-dt0)
                parts=np.array([energy2(),-before2,outgoing2,useful_step2,collision2,bath2,
                    event_kinetic2[1],event_kinetic2[2],dremoved_energy,
                    -absorbed2,-event_kinetic2[0],-dformed])
                balance2=float(parts.sum())
                if abs(balance2)>1e-8*max(1e-30,np.sum(abs(parts))):
                    raise ArithmeticError('second coefficient campaign energy mismatch')
                ledger2.append(dict(time=[cycle_index,index],field_work=receipt['coefficient2_work_J'],
                    field_loss=receipt['coefficient2_loss_J'],outgoing=outgoing2,useful=useful_step2,
                    collision=collision2,bath=float(bath2),event_kinetic=event_kinetic2.tolist(),
                    formation=dformed,recombination=dremoved_energy,absorbed=absorbed2,balance=balance2))
                # The native scheduler now consumes inherited absolute reaches;
                # only explicit source roots and local birth events seed new reach.
                local=[receipt['arrival_s'],receipt['directional_arrival_s'],receipt['coefficient2_arrival_s']]
                arrival_history=np.array([[np.inf if a is None else a for a in row] for row in local])
                if cfg.get('retain_jet_history',False):
                    transport_receipts.append(dict(time=[cycle_index,index],clock_start_s=elapsed,
                        earliest_recorded_s=[[None if not np.isfinite(a) else float(a) for a in row] for row in arrival_history],
                        field=x.tolist(),first=dx.tolist(),second=x2.tolist(),useful_coefficients_J=work_coeff.tolist(),
                        population=pop.tolist(),pool=pool.tolist(),temperature=theta.tolist(),
                        population_u=dpop.tolist(),pool_u=dpool.tolist(),temperature_u=dtheta.tolist(),
                        population_u2=pop2.tolist(),pool_u2=pool2.tolist()))
                elapsed+=dt
            useful+=dt*float(cur_load@em**2)
            duseful+=dt*float((0. if quadratic_amplitude_path else cur_dload@em**2)+2*(cur_load*em)@dem)
            absorbed=dt*float(power.sum());dabsorbed=dt*float(dpower.sum())
            ec=q['chemical_input_efficiency']
            er=q['chemical_recovery_efficiency']
            paid+=absorbed/cfg['heater_efficiency']+(
                formed+birth_energy)/ec-er*removed_energy
            cost_tangent=dabsorbed/cfg['heater_efficiency']+(
                dformed+dbirth_energy)/ec-er*dremoved_energy
            if quadratic_amplitude_path: paid_u+=cost_tangent
            else: dpaid+=cost_tangent
    end=(x,pop,pool,theta)
    density_u=(dpop,dpool,dtheta) if quadratic_amplitude_path else None
    dend=(dx,np.zeros_like(dpop),np.zeros_like(dpool),np.zeros_like(dtheta)) if quadratic_amplitude_path else (dx,dpop,dpool,dtheta)
    restoration_squared=sum(float(np.sum((a-b)**2)) for a,b in zip(end,start))
    drestoration_squared=2*sum(float(np.sum((a-b)*(da-db)))
        for a,b,da,db in zip(end,start,dend,dstart))
    second=(x2,dpop,dpool,dtheta) if quadratic_second_order else None
    return dict(useful_J=useful,duseful_J=duseful,paid_J=paid,dpaid_J=dpaid,
        campaign_net_J=useful-paid-horizon*cfg['auxiliary_J'],
        dcampaign_net_J=duseful-dpaid,
        restoration_squared=restoration_squared,
        drestoration_squared=drestoration_squared,
        endpoint=end,endpoint_jvp=dend,
        common_stage_atlas=atlas is not None,
        quadratic_amplitude_path=bool(quadratic_amplitude_path),
        population_pool_temperature_u_jvp=density_u,paid_u_jvp=paid_u if quadratic_amplitude_path else None,
        indexed_event_residuals=indexed_events,
        endpoint_coefficient2=second,
        useful_coefficient2_J=useful2 if quadratic_second_order else None,
        net_coefficient2_J=useful2-paid_u if quadratic_second_order else None,
        restoration_coefficient2=squared_return2(end,start,dend,second) if quadratic_second_order else None,
        population_pool_u2=(pop2,pool2) if quadratic_second_order else None,
        indexed_jet_history=transport_receipts,
        signed_jet_evolution_residual_trace=jet_residuals,
        jet_endpoint_error_bound_candidate=jet_radius.tolist() if shadow is not None else None,
        jet_receiver_work_error_bound_candidate_J=work_radius.tolist() if shadow is not None else None,
        nested_depth=depth,sparse_operator=sparse,
        coefficient2_energy_ledger=ledger2,
        campaign_discrete_reach_checked=bool(quadratic_second_order),
        global_causal_cone_admitted=False,
        scope=('one-sided quadratic control path, finite velocity; not an unrestricted density gradient' if quadratic_amplitude_path else 'fixed topology, positive population; not strict restored-net gate'))
