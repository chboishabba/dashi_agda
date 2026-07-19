#!/usr/bin/env python3
"""Plan denser checkpoints around unresolved Gamma excursions.

The output is a solver-facing schedule only. It never fabricates states or
interpolates Gamma. Crossing intervals are bisected recursively to the requested
depth; dangerous terminal states use the residence audit's recommended next
time when available.
"""
from __future__ import annotations
import argparse,json,math,os,tempfile
from pathlib import Path
from typing import Any

def atomic(path:Path,payload:dict[str,Any],pretty:bool=False)->None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2 if pretty else None,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try:os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def dyadic_points(left:float,right:float,depth:int)->list[float]:
    if not math.isfinite(left) or not math.isfinite(right) or right<=left:raise ValueError('invalid interval')
    if depth<1:raise ValueError('depth must be positive')
    denominator=2**depth
    return [left+(right-left)*i/denominator for i in range(1,denominator)]

def plan(payload:dict[str,Any],depth:int)->dict[str,Any]:
    requests=[]
    for trajectory in payload.get('trajectories',[]):
        tid=str(trajectory['trajectory_id'])
        for interval in trajectory.get('intervals',[]):
            classifications=interval.get('classifications',{})
            unresolved=sorted(float(threshold) for threshold,value in classifications.items() if value=='unresolved_crossing')
            if unresolved:
                requests.append({'trajectory_id':tid,'kind':'unresolved_crossing_refinement','from_checkpoint':interval['from_checkpoint'],'to_checkpoint':interval['to_checkpoint'],'start_time':float(interval['start_time']),'end_time':float(interval['end_time']),'thresholds':unresolved,'requested_times':dyadic_points(float(interval['start_time']),float(interval['end_time']),depth)})
    for terminal in payload.get('adaptive_followup_requests',[]):
        proposed=terminal.get('recommended_next_time')
        requests.append({'trajectory_id':str(terminal['trajectory_id']),'kind':'terminal_excursion_followup','terminal_checkpoint':int(terminal['terminal_checkpoint']),'terminal_time':float(terminal['terminal_time']),'terminal_gamma':float(terminal['terminal_gamma']),'threshold':float(terminal['trigger_threshold']),'requested_times':[float(proposed)] if proposed is not None else [],'requires_solver_step_size':proposed is None})
    return {'schema_version':'1.0.0','authority':{'schedule_only':True,'interpolated_state_authority':False,'truth_authority':False,'theorem_authority':False,'promoted':False},'refinement_depth':depth,'request_count':len(requests),'requests':requests,'limitations':['times request new solver output; no state or Gamma is interpolated','the solver must preserve trajectory and physical-time metadata']}

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--residence-json',type=Path,required=True);p.add_argument('--output-json',type=Path,required=True);p.add_argument('--depth',type=int,default=2);p.add_argument('--pretty',action='store_true');a=p.parse_args();r=plan(json.loads(a.residence_json.read_text()),a.depth);atomic(a.output_json,r,a.pretty);print(json.dumps({'output_json':str(a.output_json),'request_count':r['request_count']},sort_keys=True))
if __name__=='__main__':main()
