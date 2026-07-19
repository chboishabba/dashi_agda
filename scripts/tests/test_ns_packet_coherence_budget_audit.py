from __future__ import annotations
from pathlib import Path
import sys
import numpy as np
import pytest

SCRIPTS=Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:sys.path.insert(0,str(SCRIPTS))
from ns_galerkin_coherence_core import exact_alignment_budget,fit_nonnegative_dominating_coefficients
from ns_hard_alignment_derivative import hard_component_density
from ns_packet_coherence_budget_audit import audit

def taylor_green(n=8):
    x=2*np.pi*np.arange(n)/n;z,y,xg=np.meshgrid(x,x,x,indexing='ij');u=np.zeros((n,n,n,3));u[...,0]=np.sin(xg)*np.cos(y);u[...,1]=-np.cos(xg)*np.sin(y);return np.fft.fftn(u,axes=(0,1,2))

def save(path,time):np.savez(path,raw_hat=taylor_green(),nu=.02,time=time)

def checkpoint(path,index,time,gamma):
    return {'checkpoint_index':index,'source_state':str(path),'trajectory_id':'tg','time':time,'target_shell':0,'gamma':gamma,'packet_tight':True,'packet_geometry':{'local_shell_mass_fraction':.98}}

def test_exact_galerkin_rhs_and_quotient_identities():
    result=exact_alignment_budget(taylor_green(),.02,0)
    assert result['rhs_decomposition_max_residual']<1e-10
    exact=result['exact_total_derivatives'];assert exact['quotient_rule_residual']<1e-12;assert exact['component_sum_alignment_residual']<1e-10
    pressure=result['gauge_invariant_pressure'];assert pressure['raw_signed_mix_positive_part_used'] is False
    fractions=pressure['simple_top_eigenvalue_enstrophy_fraction']+pressure['top_pair_degenerate_enstrophy_fraction']+pressure['triple_degenerate_enstrophy_fraction']
    assert fractions==pytest.approx(1,abs=1e-10)

def test_hard_pressure_alignment_density_is_eigenvector_sign_invariant():
    values=np.array([[[[3.,1.,-4.]]]]);vectors=np.broadcast_to(np.eye(3),(1,1,1,3,3)).copy();omega=np.array([[[[1.,2.,3.]]]]);omega_dot=np.array([[[[.2,-.1,.3]]]])
    sdot=np.array([[[[[.4,.5,.2],[.5,-.2,.1],[.2,.1,-.2]]]]])
    reference,_=hard_component_density(values,vectors,omega,omega_dot,sdot,1e-6)
    flip1=vectors.copy();flip1[..., :,0]*=-1
    flip2=vectors.copy();flip2[..., :,1]*=-1
    assert hard_component_density(values,flip1,omega,omega_dot,sdot,1e-6)[0]==pytest.approx(reference)
    assert hard_component_density(values,flip2,omega,omega_dot,sdot,1e-6)[0]==pytest.approx(reference)

def test_nonnegative_dominating_coefficient_fit():
    x=np.array([[1.,0.,0.,0.],[0.,2.,0.,0.],[1.,1.,0.,0.]])
    y=np.array([2.,2.,3.]);fit=fit_nonnegative_dominating_coefficients(x,y,('p','c','v','t'))
    assert fit['feasible'];coef=fit['coefficients'];assert coef['p']>=2-1e-10;assert 2*coef['c']>=2-1e-10

def test_exact_audit_pointwise_tests_terminal_excursion(tmp_path):
    a=tmp_path/'a.npz';b=tmp_path/'b.npz';save(a,0);save(b,1)
    residence={'checkpoints':[checkpoint(a,0,0,0),checkpoint(b,1,1,.8)]}
    result=audit(residence,(.5,),(.01,),soft_projector_beta=8,gap_relative_floor=1e-4,allow_missing_state=False)
    parameter=result['pointwise_parameter_audits'][0]
    assert parameter['excursion_checkpoint_indices']==[1]
    assert parameter['terminal_excursion_is_pointwise_tested'] is True
    assert result['checkpoints'][0]['exact_budget_available'] is True
    assert result['checkpoints'][0]['hard_simple_spectrum_alignment_budget']['gauge_invariant_under_independent_eigenvector_signs'] is True
    assert result['interval_absorption_audits'][0]['intervals'][0]['parabolic_duration']>0
    assert result['authority']['cutoff_uniform_authority'] is False

def test_state_time_mismatch_and_missing_state_fail_closed(tmp_path):
    state=tmp_path/'s.npz';save(state,0)
    residence={'checkpoints':[checkpoint(state,0,1,0)]}
    with pytest.raises(ValueError,match='state time mismatch'):audit(residence,(.5,),(.1,))
    missing={'checkpoints':[checkpoint(tmp_path/'missing.npz',0,0,0)]}
    with pytest.raises(FileNotFoundError):audit(missing,(.5,),(.1,))
    allowed=audit(missing,(.5,),(.1,),allow_missing_state=True);assert allowed['checkpoints'][0]['exact_budget_available'] is False
