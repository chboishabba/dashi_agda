"""Fixed-support spherical campaign Jacobian-vector product, original owners.
Actual reaction/event, thermal, collision, reciprocal Whitney and indexed Cayley
steps are reused. This is a smooth-chart derivative, not an optimum certificate.
"""
import numpy as np
from solar_physical_causal import MASS,CHARGE
from solar_spherical_cycle import geometry
from solar_spherical_material_weld import construct
from solar_thermal_population_tangent import reaction_jvp,event_jvp,thermal_jvp,collision_jvp
from solar_material_generator_jvp import material_jvp
from solar_physical_cone import timed_step

def campaign_jvp(material,cfg,dheating,dload):
    rows,neutral,D,gyro,axis=material
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level']); n=len(vol)
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
    if not np.all(pop>0):raise ValueError('positive population support chart required')
    pool=np.asarray(q['initial_neutral_m3'],float).copy()
    theta=np.zeros(n);x=np.zeros(ne+nf+9*n)
    dpop=np.zeros_like(pop);dpool=np.zeros_like(pool)
    dtheta=np.zeros_like(theta);dx=np.zeros_like(x)
    start=(x.copy(),pop.copy(),pool.copy(),theta.copy())
    dstart=(dx.copy(),dpop.copy(),dpool.copy(),dtheta.copy())
    port=np.zeros(len(x));port[int(cfg['source_edge'])]=float(cfg['source_coupling_sqrt_inv_s'])
    source=np.outer(port,port)
    paid=dpaid=useful=duseful=0.
    term_load=np.asarray(cfg.get('terminal_load_rate_s_inv',load),float)
    term_dload=np.zeros(ne) if 'terminal_load_rate_s_inv' in cfg else dload
    tail=int(cfg.get('restoration_steps',0))
    for cycle_index in range(horizon):
        for index in range(len(src)+(tail if cycle_index==horizon-1 else 0)):
            terminal=index>=len(src)
            power=np.zeros(n) if terminal else heat[index]
            dpower=np.zeros(n) if terminal else dheat[index]
            inc=0. if terminal else src[index]
            cur_load=term_load if terminal else load
            cur_dload=term_dload if terminal else dload
            formed=removed_energy=birth_energy=0.
            dformed=dremoved_energy=dbirth_energy=0.
            for i in range(n):
                old=pop[i].copy();oldd=dpop[i].copy()
                primal,deriv=reaction_jvp(old,pool[i],rows[i]['te']+theta[i],
                    power[i],dt,q,oldd,dpool[i],dtheta[i],dpower[i])
                removed,created,newpool=primal
                dr,da,dnewpool=deriv
                sl=slice(ne+nf+9*i,ne+nf+9*i+9)
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
                vol,Dcurrent,nu,gyro,axis)
            j=material_jvp(model,vol,Dcurrent,nu,dD,dnu)
            L=np.zeros_like(model['generator']);dL=np.zeros_like(L)
            L[np.arange(ne),np.arange(ne)]=cur_load
            dL[np.arange(ne),np.arange(ne)]=cur_dload
            A=model['generator']-L-source
            dA=j['d_generator']-dL
            x,receipt=timed_step(x,A,2*inc*port,dt,mesh,
                dict(collision=model['loss'],load=L,source=source),port,inc,
                retain_local_midpoint=True,jvp=(dx,dA,np.zeros_like(x)))
            dx=np.asarray(receipt['state_jvp'],float)
            em=np.asarray(receipt['local_midpoint'][:ne],float)
            dem=np.asarray(receipt['local_midpoint_jvp'][:ne],float)
            useful+=dt*float(cur_load@em**2)
            duseful+=dt*float(cur_dload@em**2+2*(cur_load*em)@dem)
            absorbed=dt*float(power.sum());dabsorbed=dt*float(dpower.sum())
            ec=q['chemical_input_efficiency']
            er=q['chemical_recovery_efficiency']
            paid+=absorbed/cfg['heater_efficiency']+(
                formed+birth_energy)/ec-er*removed_energy
            dpaid+=dabsorbed/cfg['heater_efficiency']+(
                dformed+dbirth_energy)/ec-er*dremoved_energy
    end=(x,pop,pool,theta);dend=(dx,dpop,dpool,dtheta)
    restoration_squared=sum(float(np.sum((a-b)**2)) for a,b in zip(end,start))
    drestoration_squared=2*sum(float(np.sum((a-b)*(da-db)))
        for a,b,da,db in zip(end,start,dend,dstart))
    return dict(useful_J=useful,duseful_J=duseful,paid_J=paid,dpaid_J=dpaid,
        campaign_net_J=useful-paid-horizon*cfg['auxiliary_J'],
        dcampaign_net_J=duseful-dpaid,
        restoration_squared=restoration_squared,
        drestoration_squared=drestoration_squared,
        endpoint=end,endpoint_jvp=dend,
        scope='fixed topology, positive population; not strict restored-net gate')
