#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,math,os,tempfile
from pathlib import Path
import numpy as np
from ns_galerkin_coherence_core import exact_alignment_budget,fit_nonnegative_dominating_coefficients,load_raw_state
FEATURES=('pressure','commutator','viscous','tail')

def floats(s):
    out=tuple(sorted({float(x) for x in s.split(',') if x.strip()}))
    if not out or any(not math.isfinite(x) or x<0 for x in out): raise ValueError('bad float list')
    return out

def atomic(path,payload,pretty=False):
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2 if pretty else None,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try: os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def point(cp,pos,beta,gap,allow):
    if 'time' not in cp: raise ValueError('explicit time required')
    path=Path(str(cp.get('source_state',''))); t=float(cp['time'])
    try:
        raw,nu,state_t=load_raw_state(path)
        if state_t is not None and not math.isclose(state_t,t,abs_tol=1e-12): raise ValueError('state time mismatch')
        ex=exact_alignment_budget(raw,nu,int(cp['target_shell']),soft_beta_dimensionless=beta,gap_relative_floor=gap)
    except (FileNotFoundError,KeyError,ValueError) as e:
        if not allow: raise
        ex=None;err=str(e)
    else: err=None
    row=dict(cp);row.update(exact_galerkin_alignment_budget=ex,exact_budget_available=ex is not None,exact_budget_state_error=err,truth_authority=False,theorem_authority=False,promoted=False)
    if ex is None:return row,None
    tail=max(1-float(cp.get('packet_geometry',{}).get('local_shell_mass_fraction',0)),0)
    p={'trajectory_id':str(cp.get('trajectory_id','aggregate-trajectory')),'checkpoint_index':int(cp.get('checkpoint_index',pos)),'time':t,'gamma':float(cp['gamma']) if cp.get('gamma') is not None else None,'tight':bool(cp.get('packet_tight',False)),'tail':tail,'exact':ex}
    return row,p

def feat(p):
    a=p['exact']['candidate_absorption'];return np.array([a['pressure_positive_remainder'],a['commutator_positive_remainder'],a['viscous_positive_remainder'],p['tail']],float)

def parameter(points,threshold,kappa):
    eligible=[p for p in points if p['tight'] and p['gamma'] is not None]
    excursion=[p for p in eligible if p['gamma']>=threshold]
    x=np.vstack([feat(p) for p in eligible]) if eligible else np.zeros((0,4))
    y=np.array([max(p['exact']['exact_total_derivatives']['parabolic_normalized_alignment_derivative']+(kappa if p['gamma']>=threshold else 0),0) for p in eligible])
    fit=fit_nonnegative_dominating_coefficients(x,y,FEATURES)
    margins=[p['exact']['candidate_absorption']['local_geometric_depletion']-kappa for p in excursion]
    terminal=max((p['checkpoint_index'] for p in points),default=-1)
    return {'gamma_threshold':threshold,'kappa':kappa,'eligible_checkpoint_count':len(eligible),'excursion_checkpoint_count':len(excursion),'excursion_checkpoint_indices':[p['checkpoint_index'] for p in excursion],'terminal_excursion_is_pointwise_tested':any(p['checkpoint_index']==terminal for p in excursion),'minimum_excursion_local_depletion_minus_kappa':min(margins) if margins else None,'smallest_nonnegative_dominating_coefficients':fit}

def intervals(points):
    grouped={}
    for p in points:grouped.setdefault(p['trajectory_id'],[]).append(p)
    out=[]
    for tid,rows in sorted(grouped.items()):
        rows.sort(key=lambda p:p['time']);times=[p['time'] for p in rows]
        if len(set(times))!=len(times) or any(b<=a for a,b in zip(times,times[1:])):raise ValueError('bad chronology')
        data=[];td=tr=0
        for l,r in zip(rows,rows[1:]):
            dt=r['time']-l['time'];rate=l['exact']['parabolic_rate']
            if not math.isclose(rate,r['exact']['parabolic_rate'],rel_tol=1e-12):raise ValueError('rate mismatch')
            dtau=rate*dt;la=l['exact']['candidate_absorption'];ra=r['exact']['candidate_absorption'];integ=lambda k:.5*(la[k]+ra[k])*dtau
            d=integ('local_geometric_depletion');rem=integ('total_positive_remainder');td+=d;tr+=rem
            data.append({'from_checkpoint':l['checkpoint_index'],'to_checkpoint':r['checkpoint_index'],'physical_duration':dt,'parabolic_duration':dtau,'integrated_local_geometric_depletion':d,'integrated_positive_remainder':rem,'theta_emp_interval':rem/d if d>0 else None,'strict_absorption_margin':d-rem})
        out.append({'trajectory_id':tid,'intervals':data,'integrated_local_geometric_depletion':td,'integrated_positive_remainder':tr,'theta_emp':tr/td if td>0 else None,'strict_absorption_margin':td-tr,'empirical_absorption_strictly_below_one':td>0 and tr<td})
    return out

def audit(payload,thresholds,kappas,*,soft_projector_beta=8,gap_relative_floor=1e-4,allow_missing_state=False,**legacy):
    cps=payload.get('checkpoints')
    if not isinstance(cps,list) or not cps:raise ValueError('no checkpoints')
    rows=[];points=[]
    for i,cp in enumerate(cps):
        row,p=point(cp,i,soft_projector_beta,gap_relative_floor,allow_missing_state);rows.append(row)
        if p is not None:points.append(p)
    params=[parameter(points,t,k) for t in thresholds for k in kappas];absorb=intervals(points)
    cutoffs=[]
    for n in sorted({p['exact']['cutoff'] for p in points}):
        s=[p for p in points if p['exact']['cutoff']==n]
        cutoffs.append({'cutoff':n,'checkpoint_count':len(s),'maximum_rhs_decomposition_residual':max(p['exact']['rhs_decomposition_max_residual'] for p in s),'maximum_component_alignment_residual':max(p['exact']['exact_total_derivatives']['component_sum_alignment_residual'] for p in s),'minimum_simple_spectrum_enstrophy_fraction':min(p['exact']['gauge_invariant_pressure']['simple_top_eigenvalue_enstrophy_fraction'] for p in s)})
    return {'schema_version':'2.0.0','authority':{'finite_galerkin_derivative_exact_for_declared_soft_budget':True,'truth_authority':False,'theorem_authority':False,'cutoff_uniform_authority':False,'promoted':False},'definitions':{'E_K':'mean |omega_K|^2','N_K':'mean omega^T P_beta(S) omega','A_K':'N_K/E_K','P_beta':'exp(beta S)/trace(exp(beta S))','theta_emp':'integrated positive remainder / integrated local depletion'},'checkpoints':rows,'pointwise_parameter_audits':params,'interval_absorption_audits':absorb,'cutoff_summary':cutoffs,'cutoff_count':len(cutoffs),'uniform_candidate_tested_across_multiple_cutoffs':len(cutoffs)>=2}

def main():
    p=argparse.ArgumentParser();p.add_argument('--residence-json',type=Path,required=True);p.add_argument('--output-json',type=Path,required=True);p.add_argument('--gamma-thresholds',default='0.5,0.9,1.0');p.add_argument('--kappa-candidates',default='0.01,0.05,0.1,0.25');p.add_argument('--soft-projector-beta',type=float,default=8);p.add_argument('--gap-relative-floor',type=float,default=1e-4);p.add_argument('--allow-missing-state',action='store_true');p.add_argument('--pretty',action='store_true');a=p.parse_args();r=audit(json.loads(a.residence_json.read_text()),floats(a.gamma_thresholds),floats(a.kappa_candidates),soft_projector_beta=a.soft_projector_beta,gap_relative_floor=a.gap_relative_floor,allow_missing_state=a.allow_missing_state);atomic(a.output_json,r,a.pretty);print(json.dumps({'output_json':str(a.output_json),'checkpoint_count':len(r['checkpoints'])},sort_keys=True))
if __name__=='__main__':main()
