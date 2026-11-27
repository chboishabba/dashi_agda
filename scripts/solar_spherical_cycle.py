"""Same-state cochain thermal/chemical cycle and matched four-world comparison.
Graph incidences are barycentric support links, not measured physical faces.
Uses diagonal Hodge candidate; full consistent mass remains reference.
"""
import numpy as np
from scipy.constants import c
from solar_spherical_material_weld import construct
from solar_spherical_whitney import shell_mesh
from solar_physical_causal import event,reaction,MASS,CHARGE
from solar_earth_collision_tensor import rates
from solar_physical_cone import timed_step

def geometry(radii,level):
    xyz,s,m,d=shell_mesh(radii,level)
    # One material owner per tetrahedron: no instant shared remote material.
    vol=np.array([abs(np.linalg.det((xyz[list(t)][1:]-xyz[t[0]]).T))/6 for t in s[3]])
    pos=np.array([xyz[list(t)].mean(axis=0) for k in (1,2,3) for t in s[k]])
    ne,nf,nt=map(len,s[1:]); faces=[]
    def link(i,j,key,area):
        delta=pos[j]-pos[i]; length=np.linalg.norm(delta)
        assert length>0 and area>0
        faces.append(dict(id=key,source=i,target=j,normal=(delta/length).tolist(),area_m2=float(area)))
    for f,tri in enumerate(s[2]):
        p=xyz[list(tri)]; area=np.linalg.norm(np.cross(p[1]-p[0],p[2]-p[0]))/2
        for e in np.flatnonzero(d[1][f]):
            link(int(e),ne+f,'edge-face:%d:%d'%(e,f),area)
    from itertools import combinations
    for o,t in enumerate(s[3]):
        for e in combinations(t,2):
            j=m[1][e]; length=np.linalg.norm(xyz[e[1]]-xyz[e[0]])
            link(j,ne+nf+o,'edge-cell:%d:%d'%(j,o),vol[o]/length)
    mesh=dict(positions_m=pos.tolist(),coordinate_site=list(range(ne+nf))+np.repeat(np.arange(ne+nf,ne+nf+nt),9).tolist(),
              faces=faces,front_speed_m_s=c,scope='barycentric support graph; area is geometric support weight, not exterior flux')
    return vol,mesh,ne,nf

def cycle(material,cfg):
    rows,neutral,D,gyro,axis=material
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level']); n=len(vol)
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
    L=np.diag(load); S=np.outer(port,port)
    def energy():
        return x@x/2+cap@theta+np.einsum('is,i,s->',pop,vol,chem)
    original=(x.copy(),pop.copy(),pool.copy(),theta.copy())
    def residual(a,b):
        return [float(np.linalg.norm(u-v)/max(np.linalg.norm(u),np.linalg.norm(v),1e-30)) for u,v in zip(a,b)]
    assert int(cfg['max_cycles'])>=1 and cfg['auxiliary_J']>=0
    assert 0<cfg['heater_efficiency']<=1 and 0<q['chemical_input_efficiency']<=1 and 0<=q['chemical_recovery_efficiency']<=1
    campaign={}; preparation={}; trace=[]
    for iteration in range(int(cfg['max_cycles'])):
        initial=(x.copy(),pop.copy(),pool.copy(),theta.copy()); total={}
        for inc,p in zip(src,heat):
            before=energy(); costs=np.zeros(5)
            for i in range(n):
                r,a,pool[i]=reaction(pop[i],pool[i],rows[i]['te']+theta[i],p[i],dt,q)
                sl=slice(ne+nf+9*i,ne+nf+9*i+9)
                x[sl],pop[i],w=event(x[sl],pop[i],r,a,birth[i],vol[i])
                costs[:3]+=w; costs[3]+=vol[i]*(a@chem); costs[4]+=vol[i]*(r@chem)
            theta1=np.exp(-dt*cool/cap)*theta-np.expm1(-dt*cool/cap)*p/cool
            mid=np.exp(-dt*cool/(2*cap))*theta-np.expm1(-dt*cool/(2*cap))*p/cool
            absorbed=dt*p.sum(); bath=absorbed-cap@(theta1-theta); theta=theta1
            nu=rates([dict(r,te=r['te']+mid[i]) for i,r in enumerate(rows)],neutral)
            model=construct(cfg['radii_m'],cfg['angular_level'],np.arange(n),vol,pop*CHARGE**2/MASS,nu,gyro,axis)
            A=model['generator']-L-S
            x,w=timed_step(x,A,2*inc*port,dt,mesh,dict(collision=model['loss'],load=L,source=S),port,inc)
            channels=w['loss_channels_J']; useful=channels['load']; collision=channels['collision']
            paid=absorbed/cfg['heater_efficiency']+(costs[0]+costs[3])/q['chemical_input_efficiency']-q['chemical_recovery_efficiency']*costs[4]
            balance=energy()-before+w['outgoing_J']+useful+collision+bath+costs[1]+costs[2]+costs[4]-w['incident_J']-absorbed-costs[0]-costs[3]
            assert abs(balance)<=1e-8*max(abs(before),abs(energy()),w['incident_J'],absorbed,costs[3],1e-30)
            for k,v in dict(useful_J=useful,paid_J=paid,incident_J=w['incident_J'],outgoing_J=w['outgoing_J'],collision_J=collision,balance_abs_J=abs(balance)).items():
                total[k]=total.get(k,0.)+float(v)
        end=(x,pop,pool,theta); ret=residual(end,initial)
        for key,value in total.items(): campaign[key]=campaign.get(key,0.)+value
        trace.append(dict(cycle=iteration+1,return_residual=ret,ledger=dict(total)))
        if max(ret)<=cfg['return_rtol']:break
        if iteration+1<int(cfg['max_cycles']):
            for key,value in total.items(): preparation[key]=preparation.get(key,0.)+value
    # Periodic orbit and original reservoir return are separate obligations.
    orig=residual(end,original); restored=max(ret)<=cfg['return_rtol']
    material_restored=max(orig[1:])<=cfg['return_rtol']
    net=total['useful_J']-total['paid_J']-cfg['auxiliary_J']
    # Preparation is charged gross (no credit for its useful output); auxiliary per cycle.
    prep_paid=max(0.,preparation.get('paid_J',0.))+iteration*cfg['auxiliary_J']
    campaign_net=campaign['useful_J']-campaign['paid_J']-(iteration+1)*cfg['auxiliary_J']
    full_restored=max(orig)<=cfg['return_rtol']
    return dict(ledger=total,campaign_ledger=campaign,preparation_ledger=preparation,preparation_cost_J=prep_paid,
                campaign_net_J=campaign_net,full_original_restored=bool(full_restored),
                strict_campaign_net_J=campaign_net if full_restored else None,
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
    a=worlds['source_active']['conditional_net_J']; p=worlds['source_passive']['conditional_net_J']
    return dict(worlds=worlds,selected_passive_advantage_J=None if a is None or p is None else a-p,
                strongest_passive_certified=False,physical_admission=False)
