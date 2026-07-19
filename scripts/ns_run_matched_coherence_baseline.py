#!/usr/bin/env python3
"""End-to-end matched-cutoff Galerkin coherence baseline.

The default triad-excursion state has positive target-packet Gamma at N32,
N48, and N64, preventing held-out coefficient validation from passing without
an excursion in both training and holdout data.  The baseline also compares
four replacement depletion currencies after the self-advective candidate was
falsified.
"""
from __future__ import annotations
import argparse,json,os,tempfile
from pathlib import Path
from typing import Any
import numpy as np
from ns_depletion_currency_audit import audit as currency_audit
from ns_generate_matched_galerkin_trajectories import generate,ints
from ns_multicutoff_coherence_validation import validate
from ns_packet_coherence_budget_audit_v2 import audit as budget_audit,floats
from ns_shell_pair_transfer_audit import shell_pair_metrics

def atomic(path:Path,payload:dict[str,Any])->None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try:os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def run(cutoffs:tuple[int,...],workdir:Path,*,nu:float,shell:int,end_time:float,base_wave:int,amplitude:float,cfl:float,output_dt:float,gamma_thresholds:tuple[float,...],kappas:tuple[float,...],minimum_tightness:float,radius:int)->dict[str,Any]:
    manifest=generate(cutoffs,workdir/'states',nu=nu,shell=shell,end_time=end_time,base_wave=base_wave,amplitude=amplitude,cfl=cfl,nominal_output_dt=output_dt,threshold=min(gamma_thresholds),near_band=.1,dense_factor=4,initial_condition='triad-excursion',target_amplitude=.25)
    checkpoints=[];index=0
    for run_row in manifest['runs']:
        for state in run_row['states']:
            with np.load(state['source_state'],allow_pickle=False) as data:raw=np.asarray(data['raw_hat'],complex);state_nu=float(data['nu']);time=float(data['time'])
            transfer=shell_pair_metrics(raw,state_nu,shell,radius);tightness=transfer['local_shell_pair_gross_fraction'];checkpoints.append({'checkpoint_index':index,'trajectory_id':run_row['trajectory_id'],'source_state':state['source_state'],'time':time,'target_shell':shell,'cutoff':run_row['cutoff'],'gamma':transfer['gamma'],'packet_tight':tightness is not None and tightness>=minimum_tightness,'packet_geometry':{'local_shell_mass_fraction':tightness,'tightness_radius':radius,'semantics':'absolute target-mode transfer after shell-pair aggregation'},'shell_pair_transfer':transfer});index+=1
    residence={'schema_version':'matched-shell-pair-1.1','authority':{'finite_galerkin_only':True,'atomwise_gross_equivalence':False,'truth_authority':False,'theorem_authority':False,'promoted':False},'checkpoints':checkpoints}
    budget=budget_audit(residence,gamma_thresholds,kappas,soft_projector_beta=8,gap_relative_floor=1e-4,allow_missing_state=False)
    holdout=(f'matched-N{max(cutoffs)}',) if len(cutoffs)>1 else ()
    validation=validate([budget],gamma_thresholds,kappas,cutoffs,holdout)
    currencies=currency_audit(budget,gamma_thresholds,kappas,cutoffs,holdout,soft_beta_dimensionless=8,gap_relative_floor=1e-4)
    return {'schema_version':'1.2.0','authority':{'finite_matched_baseline':True,'nonvacuous_excursion_validation_required':True,'candidate_currency_comparison_executed':True,'cutoff_uniform_authority':False,'truth_authority':False,'theorem_authority':False,'bkm_authority':False,'clay_authority':False,'promoted':False},'trajectory_manifest':manifest,'residence_input':residence,'exact_budget':budget,'heldout_validation':validation,'depletion_currency_comparison':currencies,'holdout_trajectories':list(holdout)}

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cutoffs',default='32,48,64');p.add_argument('--workdir',type=Path,required=True);p.add_argument('--output-json',type=Path,required=True);p.add_argument('--viscosity',type=float,default=.01);p.add_argument('--target-shell',type=int,default=2);p.add_argument('--end-time',type=float,default=.01);p.add_argument('--base-wave',type=int,default=3);p.add_argument('--amplitude',type=float,default=.1);p.add_argument('--cfl',type=float,default=.2);p.add_argument('--output-dt',type=float,default=.005);p.add_argument('--gamma-thresholds',default='.5,.9,1.0');p.add_argument('--kappa-candidates',default='.01,.05,.1,.25');p.add_argument('--minimum-tightness',type=float,default=.8);p.add_argument('--tightness-radius',type=int,default=1);a=p.parse_args()
    result=run(ints(a.cutoffs),a.workdir,nu=a.viscosity,shell=a.target_shell,end_time=a.end_time,base_wave=a.base_wave,amplitude=a.amplitude,cfl=a.cfl,output_dt=a.output_dt,gamma_thresholds=floats(a.gamma_thresholds),kappas=floats(a.kappa_candidates),minimum_tightness=a.minimum_tightness,radius=a.tightness_radius);atomic(a.output_json,result);print(json.dumps({'output_json':str(a.output_json),'matched_cutoffs':result['trajectory_manifest']['matched_cutoffs'],'nonvacuous_validation_survives':result['heldout_validation']['any_nonvacuous_parameter_set_survives_holdout'],'candidate_currency_gate_survives':result['depletion_currency_comparison']['heldout_validation']['any_candidate_currency_passes_sampled_heldout_gate']},sort_keys=True))
if __name__=='__main__':main()
