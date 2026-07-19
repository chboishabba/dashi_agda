from __future__ import annotations
from pathlib import Path
import sys
import pytest

SCRIPTS=Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:sys.path.insert(0,str(SCRIPTS))
from ns_attach_explicit_timeline import attach,parse_times
from ns_multicutoff_coherence_validation import validate

def test_attach_timeline_requires_count_and_strict_order():
    payload={'export_receipts':[{'source_state':'a'},{'source_state':'b'}]}
    result=attach(payload,(0.,1.),'x');assert result['export_receipts'][1]['time']==1;assert result['timeline_receipt']['terminal_duration_assigned'] is False
    with pytest.raises(ValueError):attach(payload,(0.,),'x')
    with pytest.raises(ValueError):parse_times('1,1')

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
