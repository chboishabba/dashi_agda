#!/usr/bin/env python3
"""Physical raw_hat exporter with an explicit, validated timeline.

This calls the existing exact transfer enumerator but never infers time from
list position or a nominal window.  The number of supplied times must match the
number of states and times must be strictly increasing.  A terminal receipt has
no assigned duration.
"""
from __future__ import annotations
import argparse,json,math
from pathlib import Path
import numpy as np
from ns_triad_gamma_gap_raw_hat_export import atomic_json,export_problem

def parse_times(raw:str)->tuple[float,...]:
    values=tuple(float(x.strip()) for x in raw.split(',') if x.strip())
    if not values or any(not math.isfinite(x) for x in values):raise ValueError('times must be finite')
    if any(b<=a for a,b in zip(values,values[1:])):raise ValueError('times must be strictly increasing')
    return values

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--state',type=Path,action='append',required=True);p.add_argument('--times',required=True);p.add_argument('--trajectory-id',required=True);p.add_argument('--target-shell',type=int,default=2);p.add_argument('--max-mode-pairs',type=int,default=48);p.add_argument('--target-mode-pairs',type=int,default=24);p.add_argument('--selection',choices=('transfer','energy'),default='transfer');p.add_argument('--transfer-seed-count',type=int,default=512);p.add_argument('--transfer-rank-counts',default='1,8,64,512,2048,8192');p.add_argument('--aggregate-only',action='store_true');p.add_argument('--output-json',type=Path,required=True);a=p.parse_args()
    times=parse_times(a.times)
    if len(times)!=len(a.state):raise ValueError('time count must equal state count')
    ranks=tuple(sorted({int(x) for x in a.transfer_rank_counts.split(',') if x.strip()}));problems=[];receipts=[]
    for index,(state,time) in enumerate(zip(a.state,times)):
        with np.load(state,allow_pickle=False) as data:
            if 'time' in data and not math.isclose(float(data['time']),time,abs_tol=1e-12):raise ValueError(f'{state}: NPZ time disagrees with supplied time')
        duration=times[index+1]-time if index+1<len(times) else 0.
        problem,receipt=export_problem(state,time,duration,a.target_shell,a.max_mode_pairs,a.target_mode_pairs,a.selection,a.transfer_seed_count,ranks,a.trajectory_id,a.aggregate_only)
        receipt=dict(receipt);receipt['trajectory_id']=a.trajectory_id;receipt['time']=time;receipt['terminal_checkpoint']=index+1==len(times);receipt['duration_to_next']=duration if duration>0 else None;receipts.append(receipt)
        if problem is not None:
            problem['profiles'][0]['time']=time;problem['profiles'][0]['duration']=duration;problems.append(problem)
    payload={'schema_version':'2.0.0','script':'scripts/ns_triad_gamma_gap_raw_hat_export_timed.py','trajectory_id':a.trajectory_id,'authority':{'candidate_only':True,'truth_authority':False,'theorem_authority':False,'clay_authority':False,'promoted':False},'timeline_receipt':{'explicit_physical_times':list(times),'strictly_increasing':True,'terminal_duration_assigned':False},'coefficient_semantics':'physical Leray-projected frozen-phase finite carrier','problems':problems,'export_receipts':receipts,'limitations':['finite Galerkin states','terminal state has no residence duration','profile magnitude search freezes observed phases and polarizations']}
    atomic_json(a.output_json,payload);print(json.dumps({'output_json':str(a.output_json),'problem_count':len(problems),'receipt_count':len(receipts)},sort_keys=True))
if __name__=='__main__':main()
