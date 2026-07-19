from __future__ import annotations
from pathlib import Path
import sys
import pytest

SCRIPTS=Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:sys.path.insert(0,str(SCRIPTS))
from ns_adaptive_checkpoint_plan import plan
from ns_attach_explicit_timeline import attach,parse_times
from ns_generate_matched_galerkin_trajectories import generate
from ns_multicutoff_coherence_validation import validate

def test_attach_timeline_requires_count_and_strict_order():
    payload={'export_receipts':[{'source_state':'a'},{'source_state':'b'}]}
    result=attach(payload,(0.,1.),'x');assert result['export_receipts'][1]['time']==1;assert result['timeline_receipt']['terminal_duration_assigned'] is False
    with pytest.raises(ValueError):attach(payload,(0.,),'x')
    with pytest.raises(ValueError):parse_times('1,1')

def test_adaptive_plan_refines_crossing_and_terminal_excursion():
    payload={'trajectories':[{'trajectory_id':'x','intervals':[{'from_checkpoint':0,'to_checkpoint':1,'start_time':0.,'end_time':1.,'classifications':{'0.5':'unresolved_crossing','0.9':'certainly_safe'}}]}],'adaptive_followup_requests':[{'trajectory_id':'x','terminal_checkpoint':1,'terminal_time':1.,'terminal_gamma':.8,'trigger_threshold':.5,'recommended_next_time':1.25}]}
    result=plan(payload,2);assert result['request_count']==2
    crossing=result['requests'][0];assert crossing['requested_times']==[.25,.5,.75]
    assert result['requests'][1]['requested_times']==[1.25]

def test_matched_trajectory_generator_writes_explicit_physical_times(tmp_path):
    result=generate((8,),tmp_path,nu=.02,shell=0,end_time=.001,base_wave=1,amplitude=.2,cfl=.2,nominal_output_dt=.001,threshold=.5,near_band=.1,dense_factor=2)
    run=result['runs'][0];assert run['state_count']>=2
    times=[row['time'] for row in run['states']];assert times[0]==0;assert times[-1]==pytest.approx(.001);assert all(b>a for a,b in zip(times,times[1:]))

def exact_checkpoint(trajectory,index,cutoff,gamma=.8):
    return {'trajectory_id':trajectory,'checkpoint_index':index,'gamma':gamma,'packet_tight':True,'packet_geometry':{'local_shell_mass_fraction':.99},'exact_galerkin_alignment_budget':{'cutoff':cutoff,'exact_total_derivatives':{'parabolic_normalized_alignment_derivative':.1},'candidate_absorption':{'pressure_positive_remainder':1.,'commutator_positive_remainder':0.,'viscous_positive_remainder':0.,'local_geometric_depletion':.2}}}

def test_one_coefficient_set_is_applied_unchanged_to_holdout_and_cutoffs():
    payload={'checkpoints':[exact_checkpoint('train',0,32),exact_checkpoint('train',1,48),exact_checkpoint('holdout',2,64)]}
    result=validate([payload],(.5,),(.01,),(32,48,64),('holdout',))
    assert result['matched_cutoff_set_complete'] is True
    audit=result['parameter_audits'][0];assert audit['holdout_budget_passes'] is True;assert audit['one_coefficient_set_survives_holdout'] is True

def test_missing_required_cutoff_is_reported_not_promoted():
    payload={'checkpoints':[exact_checkpoint('train',0,32),exact_checkpoint('holdout',1,48)]}
    result=validate([payload],(.5,),(.01,),(32,48,64),('holdout',))
    assert result['missing_required_cutoffs']==[64];assert result['authority']['cutoff_uniform_authority'] is False
