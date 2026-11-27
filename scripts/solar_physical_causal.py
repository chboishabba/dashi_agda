"""Causal SI port-Hamiltonian shell and population/thermal cycle.
Conditional finite passive realization; not a fit to measured terrestrial impedance.
Uses original material ingress and existing local generator; population event
is the volume-weighted mean-velocity mixing identity of PopulationGrid.event.
"""
import json
import argparse
from pathlib import Path
import numpy as np
from scipy.constants import epsilon_0, elementary_charge as e, electron_mass as me, atomic_mass as u
from scipy.linalg import solve
from solar_physical_periodic import original, aperture, shell, dc_port
from solar_earth_collision_tensor import rates
from solar_earth_coupled_cell import generator

MASS=np.array([me,30.5*u,16*u])
CHARGE=e*np.array([-1.,1.,1.])

def event(z,n,removed,created,birth,volume):
    """Fixed padded chart, exact zero support, arbitrary birth velocities."""
    z=np.asarray(z,float).reshape(3,3); n=np.asarray(n,float)
    r=np.asarray(removed,float); c=np.asarray(created,float); b=np.asarray(birth,float)
    assert np.all(n>=0) and np.all(r>=0) and np.all(r<=n) and np.all(c>=0)
    assert abs((c-r)@CHARGE)<=1e-12*((c+r)@abs(CHARGE))
    w=volume*MASS
    scale=np.sqrt(w*n)
    assert np.all(z[n==0]==0)
    v=np.divide(np.sign(CHARGE)[:,None]*z,scale[:,None],out=np.zeros_like(z),where=scale[:,None]>0)
    a=n-r; new=a+c
    momentum=a[:,None]*v+c[:,None]*b
    vv=np.divide(momentum,new[:,None],out=np.zeros_like(v),where=new[:,None]>0)
    out=np.sign(CHARGE)[:,None]*np.sqrt(w*new)[:,None]*vv
    incoming=.5*np.sum(w*c*np.sum(b*b,axis=1))
    outgoing=.5*np.sum(w*r*np.sum(v*v,axis=1))
    mix=.5*np.sum(w*np.divide(a*c,new,out=np.zeros_like(new),where=new>0)*np.sum((v-b)**2,axis=1))
    residual=(np.sum(out*out)-np.sum(z*z))/2-incoming+outgoing+mix
    assert abs(residual)<=1e-10*max(incoming,outgoing,mix,np.sum(z*z),1e-30)
    return out.ravel(),new,np.array([incoming,outgoing,mix])

def reaction(n,neutral,temperature,power,dt,q):
    """Two charge-neutral ionization/recombination channels.
    Explicit nonnegative rate parameters; donor reservoir tracks ion counts.
    No rate coefficients inferred from radar density differences.
    """
    alpha=np.asarray(q['recombination_m3_s'],float)
    k=np.asarray(q['ionization_s_inv'],float)
    activation=np.asarray(q['heater_ionization_per_J'],float)
    threshold=np.asarray(q.get('activation_temperature_K',[0.,0.]),float)
    assert threshold.shape==(2,) and np.all(threshold>=0) and temperature>0
    assert alpha.shape==k.shape==activation.shape==(2,)
    assert np.all(alpha>=0) and np.all(k>=0) and np.all(activation>=0)
    neutral=np.asarray(neutral,float)
    # First recombine, then ionize available neutral precursor; both pairwise.
    r=n[1:]*(-np.expm1(-dt*alpha*n[0]))
    pool=neutral+r
    c=pool*(-np.expm1(-dt*(k*np.exp(-threshold/temperature)+activation*power)))
    return np.r_[r.sum(),r],np.r_[c.sum(),c],pool-c

def local_padded(D,nu,gyro,b,load):
    """Retain all species slots even when the donor generator omits zero D."""
    active=np.flatnonzero(D>0)
    a,_,_=generator(D,nu,gyro,b,epsilon_0,load)
    idx=np.r_[np.arange(3),np.concatenate([np.arange(3+3*j,6+3*j) for j in active]) if len(active) else np.empty(0,int)]
    out=np.zeros((12,12)); out[np.ix_(idx,idx)]=a
    return out

class Shell:
    """Real passive state-space realization: z'= (J-R)z+Bv; i=B^Tz+Dv.
    R and D split useful ground dissipation from other losses.
    """
    def __init__(self,cfg):
        self.J=np.asarray(cfg['J_s_inv'],float); self.B=np.asarray(cfg['B'],float)
        self.Rg=np.asarray(cfg['R_ground_s_inv'],float); self.Ro=np.asarray(cfg['R_other_s_inv'],float)
        self.Dg=np.asarray(cfg['D_ground_S'],float); self.Do=np.asarray(cfg['D_other_S'],float)
        self.R=self.Rg+self.Ro; self.D=self.Dg+self.Do
        m=len(self.J); assert self.J.shape==(m,m) and self.B.shape==(m,6)
        assert np.allclose(self.J+self.J.T,0)
        for a,d in ((self.Rg,m),(self.Ro,m),(self.Dg,6),(self.Do,6)):
            assert a.shape==(d,d) and np.allclose(a,a.T)
            assert np.min(np.linalg.eigvalsh(a))>=-1e-14
    def admittance(self,f):
        return self.D+self.B.T@solve(2j*np.pi*f*np.eye(len(self.J))-self.J+self.R,self.B)
    def audit_radial(self,cfg,frequencies):
        dy,dg=dc_port(cfg); out=[]
        for f in frequencies:
            y,g=shell(f,cfg['ground_admittance_normalized'],cfg['shell_sigma_S_m'],dy,dg)
            z=self.admittance(f)
            T=solve(2j*np.pi*f*np.eye(len(self.J))-self.J+self.R,self.B)
            ground=self.Dg+T.conj().T@self.Rg@T
            out.append(dict(f_Hz=float(f),relative_admittance_error=float(np.linalg.norm(z-np.diag(y))/max(np.linalg.norm(y),1e-30)),
                relative_ground_form_error=float(np.linalg.norm(ground-np.diag(abs(g)**2))/max(np.linalg.norm(abs(g)**2),1e-30))))
        return out

def advance(material,cfg,state,incident,heating,dt,sh):
    rows,neutral,D,gyro,b=material; n=len(rows)
    x,z,pop,pool,theta=map(np.copy,state)
    vol=np.asarray(cfg['volumes_m3']); capacity=np.asarray(cfg['heat_capacity_J_K']); cooling=np.asarray(cfg['cooling_W_K'])
    heating=np.asarray(heating,float); assert np.all(heating>=0) and np.all(capacity>0) and np.all(cooling>0)
    q=cfg['kinetics']; chem=np.asarray(q['formation_J_per_particle'],float)
    birthvel=np.asarray(q['birth_velocity_m_s'],float)
    assert chem.shape==(3,) and np.all(chem>=0) and birthvel.shape==(n,3,3)
    before=.5*(x@x+z@z)+capacity@theta+np.einsum('is,i,s->',pop,vol,chem)
    ledger=dict(birth_kinetic_J=0.,removed_kinetic_J=0.,mixing_J=0.,formation_J=0.,recombination_J=0.)
    for i in range(n):
        r,c,pool[i]=reaction(pop[i],pool[i],rows[i]['te']+theta[i],heating[i],dt,q)
        sl=slice(12*i+3,12*i+12)
        x[sl],pop[i],w=event(x[sl],pop[i],r,c,birthvel[i],vol[i])
        for key,v in zip(('birth_kinetic_J','removed_kinetic_J','mixing_J'),w): ledger[key]+=float(v)
        ledger['formation_J']+=float(vol[i]*(c@chem)); ledger['recombination_J']+=float(vol[i]*(r@chem))
    # Heating energy reserved for thermal storage, chemical formation paid separately.
    a=np.exp(-dt*cooling/capacity); beta=-np.expm1(-dt*cooling/capacity)/cooling
    newtheta=a*theta+beta*heating
    mid=np.exp(-dt*cooling/(2*capacity))*theta- np.expm1(-dt*cooling/(2*capacity))*heating/cooling
    bath=float(dt*heating.sum()-capacity@(newtheta-theta))
    nu=rates([dict(r,te=r['te']+mid[i]) for i,r in enumerate(rows)],neutral)
    K=np.asarray(cfg['curl_s_inv'],float); d=len(x); assert K.shape==(d,d) and np.allclose(K+K.T,0)
    A=K.copy(); load=np.asarray(cfg['load_S_m'],float); assert np.all(load>=0)
    for i in range(n):
        sl=slice(12*i,12*i+12)
        A[sl,sl]+=local_padded(pop[i]*CHARGE**2/MASS,nu[i],gyro[i],b[i],load[i])
        # Zero slots must not couple to supplied curl.
        for j in np.flatnonzero(pop[i]==0):
            ix=np.arange(12*i+3+3*j,12*i+6+3*j)
            assert np.all(K[ix,:]==0) and np.all(K[:,ix]==0)
    E=np.concatenate([np.arange(12*i,12*i+3) for i in range(n)])
    C=np.zeros((6,d)); C[:,E]=aperture(cfg['normals'],cfg['areas_m2'],vol,cfg['ned_to_cartesian'])
    c=np.asarray(cfg['source_port_sqrt_inv_s'],float)
    H=np.block([[A-C.T@sh.D@C-np.outer(c,c),-C.T@sh.B.T],[sh.B@C,sh.J-sh.R]])
    v=np.r_[x,z]; force=np.r_[2*incident*c,np.zeros(len(z))]
    I=np.eye(len(v)); nxt=solve(I-dt*H/2,(I+dt*H/2)@v+dt*force)
    xm=(v[:d]+nxt[:d])/2; zm=(v[d:]+nxt[d:])/2; port=C@xm
    natural=dt*incident**2; outgoing=dt*(xm@c-incident)**2
    material=-dt*xm@A@xm; useful=dt*sum(load[i]/epsilon_0*np.sum(xm[12*i:12*i+3]**2) for i in range(n))
    ground=dt*(zm@sh.Rg@zm+port@sh.Dg@port)
    other=dt*(zm@sh.Ro@zm+port@sh.Do@port)
    x,z=nxt[:d],nxt[d:]
    after=.5*(x@x+z@z)+capacity@newtheta+np.einsum('is,i,s->',pop,vol,chem)
    absorbed=dt*heating.sum(); r=after-before+outgoing+material+ground+other+bath+ledger['removed_kinetic_J']+ledger['mixing_J']+ledger['recombination_J']-natural-absorbed-ledger['birth_kinetic_J']-ledger['formation_J']
    scale=max(abs(after),abs(before),natural,absorbed,ledger['formation_J'],1e-30)
    assert abs(r)<=1e-8*scale
    eta=cfg['heater_efficiency']; ec=q['chemical_input_efficiency']; er=q['chemical_recovery_efficiency']
    assert 0<eta<=1 and 0<ec<=1 and 0<=er<=1
    paid=absorbed/eta+(ledger['formation_J']+ledger['birth_kinetic_J'])/ec-er*ledger['recombination_J']
    ledger.update(incident_J=float(natural),outgoing_J=float(outgoing),collision_J=float(material-useful),load_J=float(useful),ground_J=float(ground),shell_other_J=float(other),cooling_J=bath,absorbed_J=float(absorbed),paid_J=float(paid),balance_J=float(r))
    return (x,z,pop,pool,newtheta),ledger

def cycle(material,cfg):
    sh=Shell(cfg['causal_shell']); D=material[2]; n=len(D)
    pop=D*MASS/CHARGE**2; pool=np.asarray(cfg['kinetics']['initial_neutral_m3'],float)
    assert pool.shape==(n,2) and np.all(pool>=0)
    src=np.asarray(cfg['incident_sqrt_W'],float); heat=np.asarray(cfg['heating_W'],float)
    assert heat.shape==(len(src),n) and len(src)>0
    assert int(cfg.get('max_cycles',1))>=1 and cfg['auxiliary_J']>=0
    assert np.allclose(pop@CHARGE,0,atol=1e-12*max(np.max(pop),1.)*e)
    dt=cfg['period_s']/len(src); assert dt>0
    state=(np.zeros(len(cfg['curl_s_inv'])),np.zeros(len(sh.J)),pop,pool,np.zeros(n))
    start=tuple(a.copy() for a in state); hist=[]; ledger={}
    for cycle_index in range(int(cfg.get('max_cycles',1))):
        start=tuple(a.copy() for a in state); hist=[]; ledger={}
        for a,p in zip(src,heat):
            state,w=advance(material,cfg,state,a,p,dt,sh); hist.append(tuple(v.copy() for v in state))
            for k,v in w.items(): ledger[k]=ledger.get(k,0.)+v
        residual=[float(np.linalg.norm(a-b)/max(np.linalg.norm(a),np.linalg.norm(b),1e-30)) for a,b in zip(state,start)]
        if max(residual)<=cfg.get('return_rtol',1e-8): break
    restored=max(residual)<=cfg.get('return_rtol',1e-8)
    # A periodic orbit reached after transient may not restore original material.
    original_population_residual=float(np.linalg.norm(state[2]-D*MASS/CHARGE**2)/max(np.linalg.norm(D*MASS/CHARGE**2),1e-30))
    original_restored=restored and original_population_residual<=cfg.get('return_rtol',1e-8)
    net=ledger['load_J']+ledger['ground_J']-ledger['paid_J']-cfg['auxiliary_J']
    return dict(restored=bool(restored),original_population_restored=bool(original_restored),original_population_residual=original_population_residual,return_residuals=residual,cycles=cycle_index+1,ledger=ledger,net_J=float(net),admissible_cycle_net_J=float(net) if original_restored else None,radial_audit=sh.audit_radial(cfg,cfg.get('audit_frequencies_Hz',[0.,3.915,7.83])),physical_admission=False)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('root',type=Path); p.add_argument('packet',type=Path); p.add_argument('config',type=Path); a=p.parse_args()
    cfg=json.loads(a.config.read_text()); print(json.dumps(cycle(original(a.root,a.packet,cfg['row_keys'],cfg['history']),cfg),indent=2))
