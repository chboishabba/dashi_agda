#!/usr/bin/env python3
"""Fit one coefficient set and validate it non-vacuously on held-out flows."""
from __future__ import annotations
import argparse,json,math,os,tempfile
from pathlib import Path
from typing import Any
import numpy as np
from ns_galerkin_coherence_core import fit_nonnegative_dominating_coefficients
FEATURES=('pressure','commutator','viscous','tail')

def floats(raw:str)->tuple[float,...]:
    out=tuple(sorted({float(x.strip()) for x in raw.split(',') if x.strip()}))
    if not out or any(not math.isfinite(x) or x<0 for x in out):raise ValueError('bad float list')
    return out

def ints(raw:str)->tuple[int,...]:
    out=tuple(sorted({int(x.strip()) for x in raw.split(',') if x.strip()}))
    if not out or any(x<1 for x in out):raise ValueError('bad cutoff list')
    return out

def atomic(path:Path,payload:dict[str,Any],pretty:bool=False)->None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2 if pretty else None,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try:os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def collect(payloads:list[dict[str,Any]])->list[dict[str,Any]]:
    rows=[]
    for payload in payloads:
        for cp in payload.get('checkpoints',[]):
            ex=cp.get('exact_galerkin_alignment_budget')
            if not isinstance(ex,dict):continue
            a=ex['candidate_absorption'];tightness=float(cp.get('packet_geometry',{}).get('local_shell_mass_fraction',0.))
            rows.append({'trajectory_id':str(cp.get('trajectory_id','aggregate-trajectory')),'checkpoint_index':int(cp.get('checkpoint_index',len(rows))),'cutoff':int(ex['cutoff']),'gamma':float(cp['gamma']) if cp.get('gamma') is not None else None,'tight':bool(cp.get('packet_tight',False)),'a_dot':float(ex['exact_total_derivatives']['parabolic_normalized_alignment_derivative']),'features':np.asarray([a['pressure_positive_remainder'],a['commutator_positive_remainder'],a['viscous_positive_remainder'],max(1-tightness,0.)],float),'local_depletion':float(a['local_geometric_depletion'])})
    return rows

def validate(payloads:list[dict[str,Any]],thresholds:tuple[float,...],kappas:tuple[float,...],required_cutoffs:tuple[int,...],holdout_trajectories:tuple[str,...])->dict[str,Any]:
    rows=collect(payloads)
    if not rows:raise ValueError('no exact checkpoint rows')
    trajectories=sorted({r['trajectory_id'] for r in rows})
    if holdout_trajectories:
        missing=sorted(set(holdout_trajectories)-set(trajectories))
        if missing:raise ValueError(f'unknown holdout trajectories: {missing}')
        holdout=set(holdout_trajectories)
    elif len(trajectories)>1:holdout={trajectories[-1]}
    else:holdout=set()
    train=[r for r in rows if r['trajectory_id'] not in holdout and r['tight'] and r['gamma'] is not None]
    test=[r for r in rows if r['trajectory_id'] in holdout and r['tight'] and r['gamma'] is not None]
    if holdout and not test:raise ValueError('holdout set has no eligible rows')
    if not train:raise ValueError('training set has no eligible rows')
    audits=[]
    for threshold in thresholds:
        for kappa in kappas:
            train_exc=[r for r in train if r['gamma']>=threshold];test_exc=[r for r in test if r['gamma']>=threshold]
            x=np.vstack([r['features'] for r in train]);y=np.asarray([max(r['a_dot']+(kappa if r['gamma']>=threshold else 0.),0.) for r in train])
            fit=fit_nonnegative_dominating_coefficients(x,y,FEATURES);coeff=np.asarray([fit.get('coefficients',{}).get(name,0.) for name in FEATURES])
            margins=[];danger_margins=[]
            for r in test:
                target=max(r['a_dot']+(kappa if r['gamma']>=threshold else 0.),0.);margins.append(float(r['features']@coeff-target))
                if r['gamma']>=threshold:danger_margins.append(r['local_depletion']-kappa)
            budget_pass=bool(margins) and all(m>=-1e-10 for m in margins);depletion_pass=bool(danger_margins) and all(m>=-1e-10 for m in danger_margins);nonvacuous=bool(train_exc) and bool(test_exc)
            audits.append({'gamma_threshold':threshold,'kappa':kappa,'fit':fit,'training_row_count':len(train),'holdout_row_count':len(test),'training_excursion_count':len(train_exc),'holdout_excursion_count':len(test_exc),'nonvacuous_excursion_test':nonvacuous,'holdout_trajectories':sorted(holdout),'holdout_minimum_budget_margin':min(margins) if margins else None,'holdout_budget_passes':budget_pass,'holdout_minimum_excursion_depletion_margin':min(danger_margins) if danger_margins else None,'holdout_excursion_depletion_passes':depletion_pass if test_exc else None,'budget_coefficients_survive_holdout':budget_pass,'one_coefficient_set_survives_holdout':nonvacuous and budget_pass and depletion_pass})
    observed=sorted({r['cutoff'] for r in rows});missing_cutoffs=sorted(set(required_cutoffs)-set(observed))
    return {'schema_version':'1.1.0','authority':{'heldout_empirical_validation_only':True,'vacuous_excursion_pass_disallowed':True,'cutoff_uniform_authority':False,'truth_authority':False,'theorem_authority':False,'bkm_authority':False,'clay_authority':False,'promoted':False},'required_cutoffs':list(required_cutoffs),'observed_cutoffs':observed,'missing_required_cutoffs':missing_cutoffs,'matched_cutoff_set_complete':not missing_cutoffs,'trajectory_ids':trajectories,'holdout_trajectories':sorted(holdout),'parameter_audits':audits,'any_budget_coefficient_set_survives_holdout':any(a['budget_coefficients_survive_holdout'] for a in audits),'any_nonvacuous_parameter_set_survives_holdout':any(a['one_coefficient_set_survives_holdout'] for a in audits),'any_parameter_set_survives_holdout':any(a['one_coefficient_set_survives_holdout'] for a in audits),'limitations':['same coefficients are empirical, not analytic constants','a passing excursion gate requires excursions in both training and holdout','cutoff coverage alone is not compactness','multiple independent held-out flows are still required']}

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--input-json',type=Path,action='append',required=True);p.add_argument('--output-json',type=Path,required=True);p.add_argument('--gamma-thresholds',default='0.5,0.9,1.0');p.add_argument('--kappa-candidates',default='0.01,0.05,0.1,0.25');p.add_argument('--required-cutoffs',default='32,48,64');p.add_argument('--holdout-trajectory',action='append',default=[]);p.add_argument('--pretty',action='store_true');a=p.parse_args();payloads=[json.loads(path.read_text()) for path in a.input_json];r=validate(payloads,floats(a.gamma_thresholds),floats(a.kappa_candidates),ints(a.required_cutoffs),tuple(a.holdout_trajectory));atomic(a.output_json,r,a.pretty);print(json.dumps({'output_json':str(a.output_json),'matched_cutoff_set_complete':r['matched_cutoff_set_complete'],'any_nonvacuous_parameter_set_survives_holdout':r['any_nonvacuous_parameter_set_survives_holdout']},sort_keys=True))
if __name__=='__main__':main()
