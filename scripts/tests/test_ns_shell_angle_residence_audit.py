from __future__ import annotations
from pathlib import Path
import sys
import numpy as np
import pytest

SCRIPTS=Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:sys.path.insert(0,str(SCRIPTS))
from ns_shell_angle_residence_audit import IntervalRow,audit,classify_interval,contiguous_residence,packet_geometry

def groups(local=.9):
    return [{'p_shell_offset':0,'q_shell_offset':0,'angle_bin':4,'gross_activity':local},{'p_shell_offset':3,'q_shell_offset':0,'angle_bin':8,'gross_activity':1-local}]

def state(path,time,amplitude=1.):
    n=8;raw=np.zeros((n,n,n,3),complex);raw[0,0,2,1]=amplitude*n**3;raw[0,0,-2,1]=amplitude*n**3
    np.savez(path,raw_hat=raw,nu=.5,time=time)

def receipt(path,time,signed):
    return {'source_state':str(path),'time':time,'target_shell':1,'full_packet_signed_rate':signed,'full_packet_gross_activity':2.,'coarse_shell_angle_groups':groups()}

def test_packet_geometry_reports_shell_locality():
    g=packet_geometry(groups(.9),1);assert g['local_shell_mass_fraction']==pytest.approx(.9);assert g['effective_group_count']>1

def test_endpoint_interval_classification():
    base=dict(trajectory_id='t',from_checkpoint=0,to_checkpoint=1,start_time=0.,end_time=1.,duration=1.,parabolic_duration=.2,tight_start=True,tight_end=True)
    assert classify_interval(IntervalRow(**base,gamma_start=.8,gamma_end=.7),.5)=='certainly_dangerous'
    assert classify_interval(IntervalRow(**base,gamma_start=.2,gamma_end=.3),.5)=='certainly_safe'
    crossing=IntervalRow(**base,gamma_start=.2,gamma_end=.8)
    assert classify_interval(crossing,.5)=='unresolved_crossing'
    summary=contiguous_residence([crossing],.5);assert summary['certain_dangerous_duration_lower_bound']==0;assert summary['possible_dangerous_duration_upper_bound']==1

def test_audit_requires_explicit_strict_chronology_and_no_terminal_duration(tmp_path):
    a=tmp_path/'a.npz';b=tmp_path/'b.npz';state(a,0);state(b,1,2)
    payload={'trajectory_id':'x','export_receipts':[receipt(a,0,-1),receipt(b,1,-1)]}
    result=audit(payload,(.5,),1,.8,require_danger_followup=True)
    first,last=result['checkpoints'];assert first['duration_to_next']==pytest.approx(1);assert last['terminal_checkpoint'];assert last['duration_to_next'] is None
    duplicate={'export_receipts':[receipt(a,0,-1),receipt(b,0,-1)]}
    with pytest.raises(ValueError):audit(duplicate,(.5,),1,.8)
    reversed_payload={'export_receipts':[receipt(b,1,-1),receipt(a,0,-1)]}
    with pytest.raises(ValueError):audit(reversed_payload,(.5,),1,.8)
    reordered=audit(reversed_payload,(.5,),1,.8,allow_reorder=True);assert reordered['checkpoints'][0]['time']==0

def test_terminal_excursion_demands_followup(tmp_path):
    a=tmp_path/'a.npz';b=tmp_path/'b.npz';state(a,0);state(b,1)
    payload={'export_receipts':[receipt(a,0,-1),receipt(b,1,20)]}
    with pytest.raises(ValueError,match='later densely sampled state'):audit(payload,(.5,),1,.8)
    result=audit(payload,(.5,),1,.8,require_danger_followup=False);assert result['adaptive_followup_requests'];assert result['trajectories'][0]['threshold_audits'][0]['unresolved_interval_count']==1

def test_missing_time_and_state_fail_closed(tmp_path):
    missing=tmp_path/'missing.npz';payload={'export_receipts':[{'source_state':str(missing),'target_shell':1,'full_packet_signed_rate':1.,'full_packet_gross_activity':2.,'coarse_shell_angle_groups':groups()}]}
    with pytest.raises(FileNotFoundError):audit(payload,(1.,),1,.8)
    with pytest.raises(ValueError,match='explicit physical time'):audit(payload,(1.,),1,.8,allow_missing_state=True)
