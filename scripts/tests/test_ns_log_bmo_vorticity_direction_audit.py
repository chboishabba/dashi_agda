from __future__ import annotations
from pathlib import Path
import sys
import numpy as np
import pytest

SCRIPTS=Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:sys.path.insert(0,str(SCRIPTS))
from ns_galerkin_coherence_core import multiscale_direction_statistics
from ns_log_bmo_vorticity_direction_audit import audit

def test_antipodal_field_is_projectively_coherent():
    xi=np.zeros((8,8,8,3));parity=np.indices((8,8,8)).sum(axis=0)%2;xi[...,0]=np.where(parity==0,1.,-1.);weights=np.ones((8,8,8))
    result=multiscale_direction_statistics(xi,weights,(1,2));row=result['scale_rows'][0]
    assert row['vector_oscillation']['weighted_p99']>.9
    assert row['projective_oscillation']['weighted_p99']==pytest.approx(0,abs=1e-12)

def test_genuinely_multidirectional_field_has_projective_oscillation():
    xi=np.zeros((8,8,8,3));indices=np.indices((8,8,8)).sum(axis=0)%3
    for component in range(3):xi[...,component]=(indices==component)
    result=multiscale_direction_statistics(xi,np.ones((8,8,8)),(1,))
    assert result['scale_rows'][0]['projective_oscillation']['weighted_median']>.5

def test_direction_audit_emits_quantiles_and_explicit_time(tmp_path):
    n=8;x=2*np.pi*np.arange(n)/n;z,y,xg=np.meshgrid(x,x,x,indexing='ij');u=np.zeros((n,n,n,3));u[...,0]=np.sin(y);raw=np.fft.fftn(u,axes=(0,1,2));state=tmp_path/'s.npz';np.savez(state,raw_hat=raw,nu=.01,time=0.)
    payload={'checkpoints':[{'checkpoint_index':0,'source_state':str(state),'trajectory_id':'columnar','time':0.,'target_shell':0,'gamma':0.,'packet_tight':True}]}
    result=audit(payload,(1,2),1e-12,False);metric=result['checkpoints'][0]['direction_metric'];assert metric is not None
    projective=metric['scale_rows'][0]['projective_oscillation'];assert set(projective)=={'weighted_median','weighted_p90','weighted_p99','maximum'}
    assert result['authority']['line_field_gauge_invariant'] is True;assert result['authority']['continuum_log_bmo_hypothesis_proved'] is False

def test_missing_time_and_state_fail_closed(tmp_path):
    missing=tmp_path/'missing.npz';payload={'checkpoints':[{'source_state':str(missing),'target_shell':1}]}
    with pytest.raises(ValueError,match='explicit checkpoint time'):audit(payload,(1,),1e-12,False)
    payload['checkpoints'][0]['time']=0.
    with pytest.raises(FileNotFoundError):audit(payload,(1,),1e-12,False)
    result=audit(payload,(1,),1e-12,True);assert result['checkpoints'][0]['metric_available'] is False
