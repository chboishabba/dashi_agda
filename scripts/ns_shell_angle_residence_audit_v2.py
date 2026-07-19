#!/usr/bin/env python3
"""Strict-chronology shell/angle packet residence audit."""
from __future__ import annotations
import argparse, json, math, os, tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable
import numpy as np

SCRIPT_NAME = "scripts/ns_shell_angle_residence_audit.py"

def parse_float_list(raw: str) -> tuple[float, ...]:
    values=tuple(sorted({float(x.strip()) for x in raw.split(',') if x.strip()}))
    if not values or any(not math.isfinite(x) or x<0 for x in values): raise ValueError('thresholds must be finite and nonnegative')
    return values

def parse_args() -> argparse.Namespace:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input-json',type=Path,required=True); p.add_argument('--output-json',type=Path,required=True)
    p.add_argument('--gamma-thresholds',default='0.5,0.9,1.0'); p.add_argument('--tightness-radius',type=int,default=1)
    p.add_argument('--minimum-tightness',type=float,default=.8); p.add_argument('--allow-reorder',action='store_true')
    p.add_argument('--allow-terminal-danger',action='store_true'); p.add_argument('--allow-missing-state',action='store_true')
    p.add_argument('--pretty',action='store_true'); return p.parse_args()

def atomic_json(path:Path,payload:dict[str,Any],pretty:bool=False)->None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name); json.dump(payload,h,indent=2 if pretty else None,sort_keys=True); h.write('\n'); h.flush(); os.fsync(h.fileno())
    try: os.replace(tmp,path)
    finally:
        if tmp.exists(): tmp.unlink()

def packet_dissipation_from_state(path:Path,shell:int)->dict[str,Any]:
    with np.load(path,allow_pickle=False) as d:
        raw=np.asarray(d['raw_hat'],dtype=np.complex128); nu=float(d['nu']) if 'nu' in d else 1e-3; state_time=float(d['time']) if 'time' in d else None
    if raw.ndim!=4 or raw.shape[-1]!=3 or len(set(raw.shape[:3]))!=1: raise ValueError(f'{path}: invalid raw_hat shape')
    if not math.isfinite(nu) or nu<=0: raise ValueError('viscosity must be positive')
    n=raw.shape[0]; field=np.moveaxis(raw/float(n**3),-1,0); axis=np.fft.fftfreq(n)*n
    kz,ky,kx=np.meshgrid(axis,axis,axis,indexing='ij'); norm2=kx*kx+ky*ky+kz*kz; norm=np.sqrt(norm2)
    dealias=(np.abs(kx)<=n/3)&(np.abs(ky)<=n/3)&(np.abs(kz)<=n/3); packet=(norm>=2**shell)&(norm<2**(shell+1))&dealias
    energy=np.sum(np.abs(field)**2,axis=0)
    return {'cutoff':n,'physical_viscosity':nu,'state_time':state_time,'full_packet_energy':float(np.sum(energy[packet])),'full_packet_dissipation':float(np.sum(norm2[packet]*energy[packet]))}

def normalized_groups(groups:Iterable[dict[str,Any]])->list[dict[str,Any]]:
    rows=[]; total=0.
    for g in groups:
        gross=float(g['gross_activity'])
        if not math.isfinite(gross) or gross<0: raise ValueError('gross activity must be finite and nonnegative')
        rows.append({'p_shell_offset':int(g['p_shell_offset']),'q_shell_offset':int(g['q_shell_offset']),'angle_bin':int(g['angle_bin']),'gross_activity':gross}); total+=gross
    if total<=0: raise ValueError('zero gross activity')
    for row in rows: row['mass_fraction']=row['gross_activity']/total
    return rows

def packet_geometry(groups:Iterable[dict[str,Any]],radius:int)->dict[str,Any]:
    rows=normalized_groups(groups); p=np.asarray([r['mass_fraction'] for r in rows]); positive=p[p>0]
    tight=sum(r['mass_fraction'] for r in rows if abs(r['p_shell_offset'])<=radius and abs(r['q_shell_offset'])<=radius)
    entropy=float(-np.sum(positive*np.log(positive)))
    return {'group_count':len(rows),'tightness_radius':radius,'local_shell_mass_fraction':tight,'largest_group_mass_fraction':float(np.max(p)),'effective_group_count':float(1/np.sum(p*p)),'shannon_entropy':entropy,'normalized_entropy':entropy/math.log(len(rows)) if len(rows)>1 else 0.}

@dataclass(frozen=True)
class IntervalRow:
    trajectory_id:str; from_checkpoint:int; to_checkpoint:int; start_time:float; end_time:float; duration:float; parabolic_duration:float
    gamma_start:float|None; gamma_end:float|None; tight_start:bool; tight_end:bool

def classify_interval(row:IntervalRow,threshold:float)->str:
    if not row.tight_start or not row.tight_end or row.gamma_start is None or row.gamma_end is None: return 'unavailable'
    g0,g1=float(row.gamma_start),float(row.gamma_end)
    if not math.isfinite(g0) or not math.isfinite(g1): return 'unavailable'
    if min(g0,g1)>=threshold: return 'certainly_dangerous'
    if max(g0,g1)<threshold: return 'certainly_safe'
    return 'unresolved_crossing'

def contiguous_residence(rows:list[IntervalRow],threshold:float)->dict[str,Any]:
    counts={k:0 for k in ('certainly_dangerous','certainly_safe','unresolved_crossing','unavailable')}; eligible=certain=possible=unresolved=trap=0.; current=longest=0.; cp=pp=0.
    for row in rows:
        c=classify_interval(row,threshold); counts[c]+=1
        if c!='unavailable': eligible+=row.duration; trap+=.5*(float(row.gamma_start)+float(row.gamma_end))*row.duration
        if c=='certainly_dangerous':
            certain+=row.duration; possible+=row.duration; cp+=row.parabolic_duration; pp+=row.parabolic_duration; current+=row.duration; longest=max(longest,current)
        else:
            current=0.
            if c=='unresolved_crossing': unresolved+=row.duration; possible+=row.duration; pp+=row.parabolic_duration
    return {'gamma_threshold':threshold,'eligible_interval_count':sum(counts.values())-counts['unavailable'],'certainly_dangerous_interval_count':counts['certainly_dangerous'],'certainly_safe_interval_count':counts['certainly_safe'],'unresolved_interval_count':counts['unresolved_crossing'],'unavailable_interval_count':counts['unavailable'],'eligible_duration':eligible,'certain_dangerous_duration_lower_bound':certain,'possible_dangerous_duration_upper_bound':possible,'unresolved_duration':unresolved,'certain_dangerous_duration_fraction_lower_bound':certain/eligible if eligible else None,'possible_dangerous_duration_fraction_upper_bound':possible/eligible if eligible else None,'certain_dangerous_parabolic_duration':cp,'possible_dangerous_parabolic_duration':pp,'longest_contiguous_certain_dangerous_duration':longest,'trapezoid_time_average_gamma':trap/eligible if eligible else None}

def _explicit_time(receipt:dict[str,Any],metrics:dict[str,Any]|None)->float:
    if 'time' in receipt: value=float(receipt['time'])
    elif metrics is not None and metrics.get('state_time') is not None: value=float(metrics['state_time'])
    else: raise ValueError('every checkpoint requires an explicit physical time in the receipt or NPZ state')
    if not math.isfinite(value): raise ValueError('checkpoint time must be finite')
    return value

def audit(payload:dict[str,Any],thresholds:tuple[float,...],radius:int,minimum_tightness:float,duration_override:float|None=None,allow_missing_state:bool=False,*,allow_reorder:bool=False,require_danger_followup:bool=True)->dict[str,Any]:
    del duration_override
    receipts=payload.get('export_receipts')
    if not isinstance(receipts,list) or not receipts: raise ValueError('input JSON has no export_receipts')
    grouped:dict[str,list[dict[str,Any]]]={}
    for index,r in enumerate(receipts):
        path=Path(str(r.get('source_state',''))); shell=int(r['target_shell']); trajectory=str(r.get('trajectory_id',payload.get('trajectory_id','aggregate-trajectory'))); geometry=packet_geometry(r.get('coarse_shell_angle_groups',[]),radius)
        try: metrics=packet_dissipation_from_state(path,shell)
        except (FileNotFoundError,KeyError,ValueError) as exc:
            if not allow_missing_state: raise
            metrics=None; state_error=str(exc)
        else: state_error=None
        time=_explicit_time(r,metrics); signed=float(r['full_packet_signed_rate']); gross=float(r['full_packet_gross_activity']); gamma=cutoff=nu=diss=None
        if metrics is not None:
            cutoff=int(metrics['cutoff']); nu=float(metrics['physical_viscosity']); diss=float(metrics['full_packet_dissipation']); gamma=max(signed,0)/(2*nu*diss) if diss>0 else None
        grouped.setdefault(trajectory,[]).append({'checkpoint_index':index,'source_state':str(path),'trajectory_id':trajectory,'time':time,'target_shell':shell,'cutoff':cutoff,'physical_viscosity':nu,'full_packet_signed_rate':signed,'full_packet_gross_activity':gross,'signed_to_gross_ratio':signed/gross if gross>0 else None,'full_packet_dissipation':diss,'gamma':gamma,'packet_geometry':geometry,'minimum_tightness':minimum_tightness,'packet_tight':geometry['local_shell_mass_fraction']>=minimum_tightness,'gamma_available':gamma is not None,'state_error':state_error,'terminal_checkpoint':False,'duration_to_next':None,'parabolic_duration_to_next':None,'truth_authority':False,'theorem_authority':False,'promoted':False})
    checkpoints=[]; trajectories=[]; requests=[]; min_threshold=min(thresholds)
    for tid,original in sorted(grouped.items()):
        times=[r['time'] for r in original]
        if len(set(times))!=len(times): raise ValueError(f'trajectory {tid}: duplicate checkpoint times')
        increasing=all(b>a for a,b in zip(times,times[1:]))
        if not increasing and not allow_reorder: raise ValueError(f'trajectory {tid}: receipt order is not strictly chronological')
        ordered=sorted(original,key=lambda r:r['time']); intervals=[]; interval_json=[]
        for left,right in zip(ordered,ordered[1:]):
            dt=right['time']-left['time']
            if dt<=0: raise ValueError('nonpositive interval')
            if left['target_shell']!=right['target_shell']: raise ValueError('target shell changes within interval')
            if left['physical_viscosity'] is None or right['physical_viscosity'] is None: parabolic=0.
            else:
                if not math.isclose(left['physical_viscosity'],right['physical_viscosity'],rel_tol=1e-12): raise ValueError('viscosity changes within interval')
                parabolic=left['physical_viscosity']*2**(2*left['target_shell'])*dt
            left['duration_to_next']=dt; left['parabolic_duration_to_next']=parabolic
            row=IntervalRow(tid,left['checkpoint_index'],right['checkpoint_index'],left['time'],right['time'],dt,parabolic,left['gamma'],right['gamma'],left['packet_tight'],right['packet_tight']); intervals.append(row)
            interval_json.append({'from_checkpoint':row.from_checkpoint,'to_checkpoint':row.to_checkpoint,'start_time':row.start_time,'end_time':row.end_time,'duration':row.duration,'parabolic_duration':row.parabolic_duration,'gamma_start':row.gamma_start,'gamma_end':row.gamma_end,'gamma_min':min(row.gamma_start,row.gamma_end) if row.gamma_start is not None and row.gamma_end is not None else None,'gamma_max':max(row.gamma_start,row.gamma_end) if row.gamma_start is not None and row.gamma_end is not None else None,'classifications':{str(t):classify_interval(row,t) for t in thresholds}})
        terminal=ordered[-1]; terminal['terminal_checkpoint']=True
        if terminal['packet_tight'] and terminal['gamma'] is not None and terminal['gamma']>=min_threshold:
            prior=intervals[-1].duration if intervals else None; requests.append({'trajectory_id':tid,'terminal_checkpoint':terminal['checkpoint_index'],'terminal_time':terminal['time'],'terminal_gamma':terminal['gamma'],'trigger_threshold':min_threshold,'recommended_next_time':terminal['time']+.25*prior if prior else None,'reason':'terminal excursion has no following checkpoint; residence is unresolved'})
        checkpoints.extend(ordered); trajectories.append({'trajectory_id':tid,'checkpoint_count':len(ordered),'interval_count':len(intervals),'input_order_was_chronological':increasing,'intervals':interval_json,'threshold_audits':[contiguous_residence(intervals,t) for t in thresholds]})
    if requests and require_danger_followup: raise ValueError('terminal excursion requires a later densely sampled state; use --allow-terminal-danger only to emit the request')
    return {'schema_version':'2.0.0','script':SCRIPT_NAME,'authority':{'candidate_only':True,'truth_authority':False,'theorem_authority':False,'bkm_authority':False,'clay_authority':False,'promoted':False},'definition':{'gamma':'max(signed_rate,0)/(2*nu*dissipation)','interval_semantics':'endpoint lower/upper classification; no terminal duration','tightness_radius':radius,'minimum_tightness':minimum_tightness,'gamma_thresholds':list(thresholds)},'checkpoints':checkpoints,'trajectories':trajectories,'adaptive_followup_requests':requests,'limitations':['finite saved checkpoints','crossing intervals require denser output','shell tightness is not spatial compactness','no cutoff-uniform authority']}

def main()->None:
    a=parse_args(); result=audit(json.loads(a.input_json.read_text()),parse_float_list(a.gamma_thresholds),a.tightness_radius,a.minimum_tightness,allow_missing_state=a.allow_missing_state,allow_reorder=a.allow_reorder,require_danger_followup=not a.allow_terminal_danger); atomic_json(a.output_json,result,a.pretty); print(json.dumps({'output_json':str(a.output_json),'checkpoint_count':len(result['checkpoints']),'followup_request_count':len(result['adaptive_followup_requests'])},sort_keys=True))
