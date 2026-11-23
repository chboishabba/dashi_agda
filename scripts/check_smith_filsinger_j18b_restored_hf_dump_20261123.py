#!/usr/bin/env python3
"""Native J12 + conditional J18 switched HF tank restored-cycle inverse controls.
All fixtures dimensionless; spark-gap was constructed as a bank-to-HF transfer,
not a metered Filsinger load nor a new independent source.
"""
import hashlib
import json
import argparse
import numpy as np
from pathlib import Path
import check_smith_filsinger_j18_hf_spark_tank_20261123 as hf

HF_SHA = 'fa087da45f63cf6d8a5f02037e6242475ea93739'
T=20*np.pi
P=dict(Von=.003,Voff=.0009,source_amp=1.2)

def restored(options,phase=.3,tol=2e-5,max_iter=12):
    p=P|options
    x=np.zeros(9); on=False
    for n in range(max_iter):
        y,after,r=hf.advance(p,p['source_amp']>0,phase,state=x,active=on,t0=n*T)
        delta=float(np.max(abs(y-x)))
        if delta < tol and after==on:
            z,after2,final=hf.advance(p,p['source_amp']>0,phase,
                state=y,active=after,t0=(n+1)*T)
            next_delta=float(np.max(abs(z-y)))
            labels=[v[1] for v in r['event_log']]
            labels2=[v[1] for v in final['event_log']]
            same_labels=after2==after and labels==labels2
            maxshift=max((abs(a[0]-b[0]) for a,b in zip(r['event_log'],final['event_log'])),default=0.) if same_labels else None
            if next_delta < tol and same_labels and maxshift < .02:
                return dict(case=hf.simple(final), state_closure=next_delta,
                     cycle_events=labels, event_times=[float(t) for t,_ in final['event_log']],
                     event_shift_adjacent_cycles=float(maxshift),iterations=n+2,
                     pass_restored=True)
        x=y; on=after
    return dict(pass_restored=False,closure=delta,cycle_events=[v[1] for v in r['event_log']],
                iterations=max_iter,partial=hf.simple(r))

def compact(r):
    return {k:r['case'][k] for k in ('driver','incident','outgoing','net_wave',
       'hf_transfer','secondary_coupling_exchange','hf_load','gap_heat','hf_coil_heat',
       'freewheel_heat','storage_delta','residual','switches')} | {
       'closure':r['state_closure'], 'event_shift_adjacent_cycles':r['event_shift_adjacent_cycles'],
       'iterations':r['iterations']}

def core():
    tests={}
    for name,opt in [('driver_only',{'source_amp':0.}),
          ('wave_0p8',{'source_amp':.8}),('positive_1p2',{})]:
        r=restored(opt)
        assert r['pass_restored'], (name,r)
        tests[name]=compact(r)
    assert tests['driver_only']['net_wave']<0
    assert tests['wave_0p8']['net_wave']<0
    assert tests['positive_1p2']['net_wave']>0
    assert tests['positive_1p2']['hf_load']>0
    # Counterexample: HF sink disconnected; insufficient iterations to certify.
    no_load=restored({'Gload':0.},max_iter=4)
    assert not no_load['pass_restored']
    assert no_load['partial']['hf_load']==0
    return dict(status='PASS_CONDITIONAL_RESTORED',tests=tests,
         no_load_control=dict(status='NO_RESTORATION_CERTIFICATE_IN_FOUR_CYCLES',
           closure=no_load['closure'],switches=no_load['partial']['switches'],
           last_cycle_work=no_load['partial']))

def pairs():
    controls={}
    for name,(left,right) in {
       'incident_amp':({'source_amp':1.195},{'source_amp':1.205}),
       'hf_magnetic_coupling':({'kh':.118},{'kh':.122}),
    }.items():
        l,r=restored(left),restored(right)
        assert l['pass_restored'] and r['pass_restored'],(name,l,r)
        match=l['cycle_events']==r['cycle_events']
        shift=max((abs(a-b) for a,b in zip(l['event_times'],r['event_times'])),default=0.) if match else None
        controls[name]=dict(event_labels_match=match,
            event_count_each=[len(l['cycle_events']),len(r['cycle_events'])],
            max_paired_shift=shift,
            both_positive=l['case']['net_wave']>0 and r['case']['net_wave']>0,
            net=[l['case']['net_wave'],r['case']['net_wave']],
            load=[l['case']['hf_load'],r['case']['hf_load']])
    return dict(status='PASS_LOCAL_PAIRS',controls=controls,
        global_event_branch_certified=False)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--stage',choices=('core','pairs','all'),default='all')
    args=parser.parse_args()
    assert hf.blob(hf.__file__)==HF_SHA
    result=dict(status='PASS_NATIVE_J12_J18_HF_LOCAL',
       native_j12_sha=hf.NATIVE_SHA,HF_augmented_sha=HF_SHA,
       stage=args.stage,actual_original_hf_circuit=False,
       original_hf_load_meter=False,source_to_receiver_calibrated=False,
       global_J16_event_branch_certified=False,agda_kernel_run=False,github_ci_used=False)
    if args.stage in ('core','all'):result['core']=core()
    if args.stage in ('pairs','all'):result['pairs']=pairs()
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
