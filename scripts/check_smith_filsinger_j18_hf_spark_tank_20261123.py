#!/usr/bin/env python3
"""J18 native-J12-compatible switched HF dump and nonlinear capacitance study.

A proposed physical *extension*, NOT a verified Filsinger wiring diagram:
charge-bank b --> on/off spark switch --> HF series L_h/R_h --> C_h(x),
with signed coupling k_h to existing J12 secondary voltage u and optional
physical HF load G_load*x^2. Source oscillator, J12 wave port, diode currents,
capacitor/magnetic energy, switching thresholds and source accounting retained.

Zero-coupling native legacy mode is checked numerically against exact J12.
HF mode is a new nine-state candidate; HF frequency is dimensionless and is
NOT the observed acoustic 7.8 kHz or source-calibrated RF.
"""
import hashlib
import json
from pathlib import Path
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
import check_smith_filsinger_j12_restored_cycles_20261122 as native

NATIVE_SHA = 'f5f66e343a979dfe2bc70f68e1e98fce75817653'
ENERGY_CHANNELS = ('driver','incident','outgoing','copper1','copper2','diode','bleed',
                   'legacy_spark_heat','field_heat','gap_heat','hf_coil_heat',
                   'freewheel_heat','hf_load','bank_to_hf','coupling_return')
DEFAULT = dict(Lh=.15, Ch=.12, alpha=.5, Rgap=.09, Rcoil=.05, Rfree=.4,
               Gload=.16, kh=.12, mode='hf')

def blob(path):
    data=Path(path).read_bytes()
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def symbolic_checks():
    b,ih,x,uh,on,Lh,Ch,alpha,rg,rc,rf,gl,kh=s.symbols(
        'b ih x uh on Lh Ch alpha rg rc rf gl kh', real=True)
    cap_charge=Ch*(x+alpha*x**3)
    cap_energy=Ch*(x*x/s.Integer(2)+s.Rational(3,4)*alpha*x**4)
    assert s.simplify(s.diff(cap_energy,x)-x*s.diff(cap_charge,x))==0
    resistance=rc+on*rg+(1-on)*rf
    idot=(on*(b-x)-resistance*ih-kh*uh)/Lh
    xdot=(on*ih-gl*x)/(Ch*(1+3*alpha*x*x))
    eh=Lh*ih*ih/2+cap_energy
    hfchange=s.factor(s.diff(eh,ih)*idot+s.diff(eh,x)*xdot)
    expected=on*b*ih-kh*uh*ih-resistance*ih*ih-gl*x*x
    assert s.simplify(hfchange-expected)==0
    assert s.simplify(hfchange+(-on*b*ih+kh*uh*ih)
                      +(resistance*ih*ih+gl*x*x))==0
    assert s.simplify(cap_charge.subs(alpha,0)-Ch*x)==0
    assert s.simplify(cap_energy.subs(alpha,0)-Ch*x*x/2)==0
    return dict(capacitor_charge=str(cap_charge),capacitor_energy=str(cap_energy),
                signed_hf_tank_power=str(expected),
                bank_and_secondary_transfer_cancel=True,checks=5)

def energy(z,p):
    i,j,u,v,b,q,r,ih,x=z
    L=np.array([[p['L1'],p['M']],[p['M'],p['L2']]])
    A=np.array([[p['C']+p['Cu'],-p['C']],[-p['C'],p['C']+p['Cv']]])
    return float(.5*np.array([i,j])@L@np.array([i,j])+
       .5*np.array([u,v])@A@np.array([u,v])+.5*p['Cb']*b*b+q*q+r*r+
       .5*p['Lh']*ih*ih+p['Ch']*(.5*x*x+.75*p['alpha']*x**4))

def advance(p,incident,phase,state=None,active=False,t0=0.,T=None,
            rtol=2e-8,atol=3e-10,max_step=.025):
    if T is None:T=native.T
    p=native.BASE|DEFAULT|p
    assert p['mode'] in ('legacy','hf')
    assert p['L1']*p['L2']>p['M']**2 and p['Lh']>0 and p['Ch']>0
    assert p['alpha']>=0 and all(p[k]>=0 for k in
       ('Gload','Rgap','Rcoil','Rfree','Gbleed','gamma_rad','gamma_internal'))
    L=np.array([[p['L1'],p['M']],[p['M'],p['L2']]])
    A=np.array([[p['C']+p['Cu'],-p['C']],[-p['C'],p['C']+p['Cv']]])
    assert np.linalg.eigvalsh(L).min()>0 and np.linalg.eigvalsh(A).min()>0
    Li=np.linalg.inv(L); Ai=np.linalg.inv(A)
    state=np.zeros(9) if state is None else np.array(state,dtype=float)
    assert state.shape==(9,)
    initial=energy(state,p)
    y=np.r_[state,np.zeros(len(ENERGY_CHANNELS))]
    on=active
    time=t0
    events=[]
    rad=np.sqrt(2*p['gamma_rad'])
    def rhs(t,y,on):
        i,j,u,v,b,q,r,ih,x=y[:9]
        drv=p.get('drive_amp',2.)*np.sin(t)
        sr=p['source_amp']*np.cos(p['omega']*t+phase) if incident else 0.
        si=p['source_amp']*np.sin(p['omega']*t+phase) if incident else 0.
        ju=max((u-b-p['Vd'])/p['Rd'],0.)
        jv=max((v-b-p['Vd'])/p['Rd'],0.)
        hf=(p['mode']=='hf')
        coupling=p['kh']*ih if hf else 0.
        ij=Li@np.array([drv-p['R1']*i,u-v-p['R2']*j])
        uv=Ai@np.array([-j-ju+p['k']*q+coupling,j-jv])
        bank=(ju+jv-p['Gbleed']*b-(on*ih if hf else p['Gspark']*on*b))/p['Cb']
        dq=p['omega']*r-(p['gamma_rad']+p['gamma_internal'])*q-p['k']*u/2+rad*sr
        dr=-p['omega']*q-(p['gamma_rad']+p['gamma_internal'])*r+rad*si
        if hf:
            resistance=p['Rcoil']+p['Rgap']*on+p['Rfree']*(not on)
            dih=(on*(b-x)-resistance*ih-p['kh']*u)/p['Lh']
            dx=(on*ih-p['Gload']*x)/(p['Ch']*(1+3*p['alpha']*x*x))
        else:
            dih=0.;dx=0.
        pout=(sr-rad*q)**2+(si-rad*r)**2
        works=[drv*i,sr*sr+si*si,pout,p['R1']*i*i,p['R2']*j*j,
               p['Vd']*(ju+jv)+p['Rd']*(ju*ju+jv*jv),
               p['Gbleed']*b*b,(not hf)*p['Gspark']*on*b*b,
               2*p['gamma_internal']*(q*q+r*r),
               hf*p['Rgap']*on*ih*ih,hf*p['Rcoil']*ih*ih,
               hf*p['Rfree']*(not on)*ih*ih,hf*p['Gload']*x*x,
               hf*on*b*ih,hf*p['kh']*u*ih]
        return np.r_[ij,uv,bank,dq,dr,dih,dx,works]
    for _ in range(700):
        if time>=t0+T-1e-10:break
        def event(t,y):return y[4]-(p['Voff'] if on else p['Von'])
        event.terminal=True;event.direction=-1 if on else 1
        sol=solve_ivp(lambda t,y:rhs(t,y,on),(time,t0+T),y,
                      events=event,rtol=rtol,atol=atol,max_step=max_step)
        assert sol.success,sol.message
        time=float(sol.t[-1]);y=sol.y[:,-1]
        if len(sol.t_events[0]):
            events.append((time-t0,'off' if on else 'on'))
            on=not on
        else:break
    else:raise RuntimeError('spark event overflow')
    named=dict(zip(ENERGY_CHANNELS,y[9:]))
    named['hf_transfer'] = named.pop('bank_to_hf')
    named['secondary_coupling_exchange'] = named.pop('coupling_return')
    named['storage_delta']=energy(y[:9],p)-initial
    named['net_wave']=named['incident']-named['outgoing']
    named['spark']=named['legacy_spark_heat'] if p['mode']=='legacy' else named['hf_transfer']
    loss_keys=('copper1','copper2','diode','bleed','legacy_spark_heat','field_heat',
               'gap_heat','hf_coil_heat','freewheel_heat','hf_load')
    named['residual']=named['driver']+named['net_wave']-sum(named[k] for k in loss_keys)-named['storage_delta']
    named['switches']=len(events)
    named['event_log']=events
    named['initial_energy']=initial
    named['final_energy']=energy(y[:9],p)
    named['hf_final_energy']=p['Lh']*y[7]**2/2+p['Ch']*(y[8]**2/2+.75*p['alpha']*y[8]**4)
    assert abs(named['residual'])<3e-5,named['residual']
    assert min(named[k] for k in loss_keys)>-1e-7
    return y[:9],on,named

def inspect_legacy():
    original=native.BASE|dict(Von=.003,Voff=.0009,source_amp=1.2)
    nstate,non,r=native.advance(original,True,.3,np.zeros(7),False,0.)
    xstate,xon,x=advance(original|dict(mode='legacy'),True,.3,
                          rtol=2e-9,atol=3e-11,max_step=.12)
    assert non==xon and x['switches']==r['switches']
    assert np.max(abs(nstate-xstate[:7]))<2e-6
    for key in ('driver','incident','outgoing','net_wave','diode','spark','storage_delta'):
        assert abs(x[key]-r[key])<1e-5,(key,x[key],r[key])
    assert x['hf_transfer']==0 and x['hf_load']==0 and x['hf_final_energy']==0
    return {'native_J12_equivalence':'PASS','max_state_diff':float(np.max(abs(nstate-xstate[:7]))),
            'signed_work_residual':float(x['residual']),'same_switch_events':len(x['event_log'])}

def simple(result):
    return {k:float(result[k]) for k in ('driver','incident','outgoing','net_wave',
       'hf_transfer','secondary_coupling_exchange','gap_heat','hf_coil_heat',
       'freewheel_heat','hf_load','diode','field_heat','legacy_spark_heat',
       'storage_delta','hf_final_energy','residual','switches')}

def main():
    assert blob(native.__file__)==NATIVE_SHA
    exact=symbolic_checks()
    old=inspect_legacy()
    parameters=native.BASE|dict(Von=.003,Voff=.0009,source_amp=1.2)
    runs={}
    for name,cfg in {
        'drive_wave_hf':dict(),
        'drive_wave_no_hf_coupling':dict(kh=0.),
        'drive_wave_linear_cap':dict(alpha=0.),
        'drive_wave_zero_load':dict(Gload=0.),
        'drive_only_hf':dict(source_amp=0.),
        'no_sources_empty':dict(source_amp=0.,drive_amp=0.),
    }.items():
        opt=parameters|cfg
        state,on,r=advance(opt,opt['source_amp']>0,.3)
        runs[name]=simple(r)
        if name=='no_sources_empty':
            assert r['hf_load']==0 and r['hf_transfer']==0 and r['driver']==0 and r['storage_delta']==0
    assert runs['drive_wave_hf']['hf_load']>0
    assert runs['drive_wave_zero_load']['hf_load']==0
    assert runs['drive_wave_no_hf_coupling']['secondary_coupling_exchange']==0
    result={'status':'PASS_NATIVE_J12_LIMIT_AND_HF_TANK_SYNTHETIC',
            'native_J12_SHA':NATIVE_SHA,'sympy_checks':exact,
            'legacy_regression':old,'cases':runs,
            'no_measured_hf_cap_material_or_device_source':True,
            'restored_cycle_claim':False,
            'HF_dump_is_internal_transfer_not_external_source':True,
            'HF_load_is_illustrative_resistive_sink_not_Filsinger_measured_output':True,
            'not_original_pin_complete_topology':True,'github_ci_used':False}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
