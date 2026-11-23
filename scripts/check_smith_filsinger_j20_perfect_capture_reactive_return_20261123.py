#!/usr/bin/env python3
"""J20 two *different* 100%-limits: matched wave port and ideal HF-load path.

Extends the exact J18 nine-state circuit ONLY by input quadrature handedness and
an OFF-phase reactive capacitor return; default original J18 behavior unchanged.
This is conditional mathematics (not a real radio/ionosphere/antigravity circuit).
"""
import hashlib
import json
from pathlib import Path
import sympy as S
import check_smith_filsinger_j19_zero_freewheel_inverse_20261123 as j19
import check_smith_filsinger_j18_hf_spark_tank_20261123 as hf

HF_SHA = 'f4270a475f010874056cfe3cdeff5ee8e43c44eb'
J19_SHA = 'cc5cec2d4f881b38b4c01ef79dd93f36e9ef1439'
COMMON = dict(wave_handedness=-1., gamma_rad=.04, off_return='capacitive', Rfree=0.)

def blob(path):
    b=Path(path).read_bytes()
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def exact():
    r,d,w=S.symbols('gamma_r gamma_i omega',positive=True)
    reflected_match=S.factor((1-2*r/(r+d))**2)
    reflected_counter=S.factor(S.simplify(S.Abs(1-2*r/(r+d+2*S.I*w))**2))
    assert S.simplify(reflected_match-(r-d)**2/(r+d)**2)==0
    assert S.simplify(reflected_match.subs(r,d))==0
    assert S.simplify(reflected_counter.subs({r:S.Rational(1,25),d:S.Rational(1,25),w:S.Rational(11,10)}))>0
    # Strict 100%-HF delivery requires all HF dissipation channels zero
    # on their occupied intervals.  This is a subcircuit identity, not an
    # environmental-to-load result.
    Rc,Rg,Rf,Ion,Ioff,Load=S.symbols('Rc Rg Rf I_on I_off Load',nonnegative=True)
    loss=Rc*(Ion+Ioff)+Rg*Ion+Rf*Ioff
    assert loss.subs({Rc:0,Rg:0,Rf:0})==0
    assert S.simplify(Load/(Load+loss)).subs({Rc:0,Rg:0,Rf:0})==1
    assert S.simplify(Load/(Load+loss)).subs({Rc:1,Rg:1,Rf:1,Load:1,Ion:1,Ioff:1})<1
    # Capacitive OFF return: inductor-to-capacitor work exactly cancels.
    Ch,alpha,Lh,ih,x,b,u,k,gl,on=S.symbols('Ch alpha Lh ih x b u k gl on',real=True)
    Q=Ch*(x+alpha*x**3); U=Ch*(x**2/2+3*alpha*x**4/4)+Lh*ih**2/2
    xd=(ih-gl*x)/S.diff(Q,x)
    id=(on*b-x-k*u-(Rc+on*Rg)*ih)/Lh
    dU=S.factor(S.diff(U,x)*xd+S.diff(U,ih)*id)
    assert S.simplify(dU-(on*b*ih-k*u*ih-(Rc+on*Rg)*ih**2-gl*x*x))==0
    return dict(matched_linear_port_reflection=str(reflected_match),
         perfect_linear_wave_capture_condition='gamma_r=gamma_i with opposite-rotating source quadratures in this convention',
         perfect_HF_subcircuit_requires='Rcoil=Rgap=Rfree=0 or no current through corresponding dissipators; zero storage drift',
         exact_reactive_return_power_balance=True, source_independent_100percent_load_established=False)

def one(name,params=None, phase=.3):
    p=COMMON|(params or {})
    r=j19.cycle(p,phase,maxiter=13,tol=2e-5)
    assert r['accepted'],(name,'not restored',r)
    d=r['work']
    assert abs(d['residual'])<3e-5 and abs(d['storage_delta'])<1e-5
    assert d['freewheel_heat']==0
    denom=sum(d[k] for k in ('hf_load','gap_heat','hf_coil_heat','freewheel_heat'))
    out=dict(label=name,parameters=p,phase=phase,
         wave_capture_fraction=d['net_wave']/d['incident'] if d['incident']>0 else None,
         HF_internal_load_fraction=d['hf_load']/denom if denom else None,
         load_over_incident=d['hf_load']/d['incident'] if d['incident']>0 else None,
         events=len(r['event_labels']), event_labels=r['event_labels'],
         event_times=r['event_times'], closure=r['closure'],
         adjacent_event_shift=r['event_shift'],
         driver=d['driver'],incoming=d['incident'],outgoing=d['outgoing'],net_wave=d['net_wave'],
         HF_load=d['hf_load'],HF_coil_loss=d['hf_coil_heat'],HF_gap_loss=d['gap_heat'],
         HF_freewheel_loss=d['freewheel_heat'],field_heat=d['field_heat'],
         bank_to_HF=d['hf_transfer'],secondary_to_HF=-d['secondary_coupling_exchange'],
         total_storage_delta=d['storage_delta'],total_work_residual=d['residual'])
    return out

def run():
    assert blob(hf.__file__)==HF_SHA
    assert blob(j19.__file__)==J19_SHA
    x=exact()
    base=one('matched_nonzero_coil_gap')
    hf100=one('ideal_100percent_HF_branch',dict(Rcoil=0.,Rgap=0.))
    joint=one('high_capture_with_100percent_HF_branch',dict(k=.05,Rcoil=0.,Rgap=0.))
    high_output=one('higher_HF_output_nonzero_losses',dict(kh=.18,Gload=.32))
    source_only=one('controller_off_wave_on',dict(drive_amp=0.))
    source_off=one('controller_on_wave_off',dict(source_amp=0.))
    minus=one('source_amplitude_minus',dict(source_amp=1.195))
    plus=one('source_amplitude_plus',dict(source_amp=1.205))
    kh_minus=one('secondary_HF_coupling_minus',dict(kh=.1195))
    kh_plus=one('secondary_HF_coupling_plus',dict(kh=.1205))
    ph_minus=one('source_phase_minus',phase=.299)
    ph_plus=one('source_phase_plus',phase=.301)
    gl_minus=one('HF_load_conductance_minus',dict(Gload=.155))
    gl_plus=one('HF_load_conductance_plus',dict(Gload=.165))
    assert abs(hf100['HF_internal_load_fraction']-1)<1e-10
    assert abs(joint['HF_internal_load_fraction']-1)<1e-10
    assert joint['wave_capture_fraction']>.999
    assert base['wave_capture_fraction']>.98 and base['HF_internal_load_fraction']>.98
    assert base['events']==hf100['events']==minus['events']==plus['events']==8
    assert source_only['HF_load']>0 and source_only['driver']==0
    assert source_off['incoming']==0 and source_off['driver']>0
    assert high_output['HF_load']>base['HF_load'] and high_output['wave_capture_fraction']>.98
    shift=max(abs(a-b) for a,b in zip(minus['event_times'],plus['event_times']))
    assert shift<.02
    shifts={}
    for key,aa,bb in [('HF_coupling',kh_minus,kh_plus),('source_phase',ph_minus,ph_plus),('HF_load_conductance',gl_minus,gl_plus)]:
        assert aa['events']==bb['events']==base['events']==8
        assert aa['event_labels']==bb['event_labels']==base['event_labels']
        shifts[key]=max(abs(a-b) for a,b in zip(aa['event_times'],bb['event_times']))
    assert shifts['HF_coupling']<.02 and shifts['source_phase']<.02
    assert shifts['HF_load_conductance']>.02  # avoid false global inverse smoothness certificate
    # This is not 100% *external-to-load* conversion. The native resonator
    # internal damping is very large in the wave-matched fixtures.
    assert joint['HF_load']/joint['incoming']<.01
    return dict(status='PASS_LOCAL_J20_EXACT_J18_SOURCE_AND_REACTIVE_MODEL',
       original_J12_blob=hf.NATIVE_SHA,extended_J18_blob=HF_SHA,J19_baseline_blob=J19_SHA,
       sympy= x,models={z['label']:z for z in (base,hf100,joint,high_output,source_only,source_off)},
       local_perturbations=dict(source_amplitude_1_195_vs_1_205={
         'same_8_event_labels':minus['event_labels']==plus['event_labels']==base['event_labels'],
         'maximum_aligned_event_time_shift':shift,
         'both_restored':True},
         HF_coupling_pm_0_0005_event_time_shift=shifts['HF_coupling'],
         phase_pm_0_001_event_time_shift=shifts['source_phase'],
         load_pm_0_005_event_time_shift=shifts['HF_load_conductance'],
         load_pair_fails_0_02_event_alignment=True),
       full_external_to_HF_load_100percent_claim=False,
       documented_original_device_100percent_physical_coupling=False,
       actual_Duga_HAARP_SURA_to_device_transfer=False,
       actual_HF_superconducting_gravity=False,
       user_data_or_experimental_meter_replayed=False,
       source_and_driver_event_branches_differ=True,
       github_actions_or_ci_run=False,agda_kernel_run=False)

if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
