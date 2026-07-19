#!/usr/bin/env python3
"""Projective multiscale vorticity-direction audit.

The line-field statistic uses M_r=E_r[xi xi^T] and
sqrt(1-lambda_max(M_r)), so antipodal directions are identified.  Vector and
projective weighted median/p90/p99/maximum values are emitted separately.
"""
from __future__ import annotations
import argparse,json,math,os,tempfile
from pathlib import Path
from typing import Any
import numpy as np
from ns_galerkin_coherence_core import frequency_grid,multiscale_direction_statistics,packet_mask

SCRIPT_NAME='scripts/ns_log_bmo_vorticity_direction_audit.py'

def ints(raw:str)->tuple[int,...]:
    out=tuple(sorted({int(x.strip()) for x in raw.split(',') if x.strip()}))
    if not out or any(x<1 for x in out): raise ValueError('radii must be positive integers')
    return out

def atomic(path:Path,payload:dict[str,Any],pretty:bool=False)->None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2 if pretty else None,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try: os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def checkpoint_metric(path:Path,shell:int,radii:tuple[int,...],floor:float,expected_time:float)->dict[str,Any]:
    with np.load(path,allow_pickle=False) as data:
        raw=np.asarray(data['raw_hat'],dtype=np.complex128);state_time=float(data['time']) if 'time' in data else None
    if state_time is not None and not math.isclose(state_time,expected_time,abs_tol=1e-12): raise ValueError('state and receipt times disagree')
    if raw.ndim!=4 or raw.shape[-1]!=3 or len(set(raw.shape[:3]))!=1: raise ValueError('invalid raw_hat shape')
    n=int(raw.shape[0]);wave,norm2,norm,dealias=frequency_grid(n);packet=packet_mask(norm,shell,dealias);hat=raw*packet[...,None]
    omega_hat=1j*np.cross(wave,hat);omega=np.fft.ifftn(omega_hat,axes=(0,1,2)).real;omega2=np.sum(omega*omega,axis=-1)
    maximum=float(np.max(omega2)) if omega2.size else 0.;active=omega2>max(1e-30,floor*maximum);weights=np.where(active,omega2,0.)
    if float(np.sum(weights))<=0: raise ValueError('target packet has zero active vorticity')
    xi=np.zeros_like(omega);xi[active]=omega[active]/np.sqrt(omega2[active])[:,None]
    result=multiscale_direction_statistics(xi,weights,radii);result.update(cutoff=n,target_shell=shell,active_enstrophy_sum=float(np.sum(weights)),active_grid_fraction=float(np.mean(active)))
    return result

def audit(payload:dict[str,Any],radii:tuple[int,...],floor:float,allow_missing_state:bool=False)->dict[str,Any]:
    cps=payload.get('checkpoints')
    if not isinstance(cps,list) or not cps: raise ValueError('no checkpoints')
    if not math.isfinite(floor) or not 0<floor<1: raise ValueError('active floor must lie in (0,1)')
    rows=[];by_cutoff={}
    for pos,cp in enumerate(cps):
        if 'time' not in cp: raise ValueError('explicit checkpoint time required')
        path=Path(str(cp.get('source_state','')));time=float(cp['time'])
        try: metric=checkpoint_metric(path,int(cp['target_shell']),radii,floor,time)
        except (FileNotFoundError,KeyError,ValueError) as exc:
            if not allow_missing_state: raise
            metric=None;err=str(exc)
        else:
            err=None;by_cutoff.setdefault(int(metric['cutoff']),[]).append(metric)
        rows.append({'checkpoint_index':int(cp.get('checkpoint_index',pos)),'trajectory_id':str(cp.get('trajectory_id','aggregate-trajectory')),'source_state':str(path),'time':time,'gamma':cp.get('gamma'),'packet_tight':bool(cp.get('packet_tight',False)),'direction_metric':metric,'metric_available':metric is not None,'state_error':err,'truth_authority':False,'theorem_authority':False,'promoted':False})
    summaries=[]
    for cutoff,metrics in sorted(by_cutoff.items()):
        summaries.append({'cutoff':cutoff,'checkpoint_count':len(metrics),'maximum_projective_log_bmo_p99':max(m['projective_log_bmo_p99_sup'] for m in metrics),'maximum_projective_log_bmo_maximum':max(m['projective_log_bmo_max_sup'] for m in metrics),'mean_projective_log_bmo_p99':float(np.mean([m['projective_log_bmo_p99_sup'] for m in metrics]))})
    return {'schema_version':'2.0.0','script':SCRIPT_NAME,'authority':{'candidate_only':True,'finite_grid_surrogate':True,'line_field_gauge_invariant':True,'continuum_log_bmo_hypothesis_proved':False,'cutoff_uniform_authority':False,'truth_authority':False,'theorem_authority':False,'bkm_authority':False,'clay_authority':False,'promoted':False},'definition':{'vector_oscillation':'sqrt(1-|E_r xi|^2)','projective_oscillation':'sqrt(1-lambda_max(E_r[xi xi^T]))','reported_statistics':['weighted_median','weighted_p90','weighted_p99','maximum'],'grid_radii':list(radii),'active_relative_floor':floor},'checkpoints':rows,'cutoff_summary':summaries,'cutoff_count':len(summaries),'uniform_candidate_tested_across_multiple_cutoffs':len(summaries)>=2,'limitations':['finite periodic grid','finite radii','RMS/projective surrogate rather than exact continuum mean oscillation','no interpolation between radii or times','no cutoff-uniform authority']}

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--residence-json',type=Path,required=True);p.add_argument('--output-json',type=Path,required=True);p.add_argument('--grid-radii',default='1,2,4,8');p.add_argument('--active-relative-floor',type=float,default=1e-12);p.add_argument('--allow-missing-state',action='store_true');p.add_argument('--pretty',action='store_true');a=p.parse_args();r=audit(json.loads(a.residence_json.read_text()),ints(a.grid_radii),a.active_relative_floor,a.allow_missing_state);atomic(a.output_json,r,a.pretty);print(json.dumps({'output_json':str(a.output_json),'checkpoint_count':len(r['checkpoints']),'cutoff_count':r['cutoff_count']},sort_keys=True))
if __name__=='__main__':main()
