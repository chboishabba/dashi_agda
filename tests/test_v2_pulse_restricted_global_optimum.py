"""Analytic globally optimal q within the stated scalar pulse-window family only."""
import sys
from pathlib import Path
from dataclasses import replace
import math
import pytest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from check_v2_pulse_nonlinear_recovery import Candidate,pulse_window
from v2_pulse_restricted_global_optimum import derivative_identity,restricted_global_optimum


def test_exact_symbolic_derivative_and_monotone_numerator():
    d=derivative_identity()
    assert d['first_derivative_exact'] and d['unique_zero_derivative_exact']


@pytest.mark.parametrize('model',[
    Candidate(),
    Candidate(switch_per_i2_j_per_a2=.015),
    Candidate(switch_per_i2_j_per_a2=0.),
    Candidate(current_limit_a=7.),
])
def test_global_closed_form_optimality_against_dense_finite_candidates(model):
    r=restricted_global_optimum(model)
    q=r['selected_q_global']
    assert 0<=q<=r['q_max_from_current']
    assert r['grid_gap_w']>=-1e-7
    for k in range(201):
        sample_q=.999999*r['q_max_from_current']*k/200
        a=pulse_window(model,sample_q)
        assert r['optimum']['ideal_net_bus_w']>=a['ideal_net_bus_w']-1e-7
    assert abs(r['optimum']['complete_balance_residual_w'])<1e-9


def test_no_switch_current_cost_optimises_at_current_boundary():
    r=restricted_global_optimum(Candidate(switch_per_i2_j_per_a2=0.))
    assert abs(r['selected_q_global']-r['q_max_from_current'])<1e-12


def test_switching_current_loss_shifts_optimum_to_wider_pulses():
    base=restricted_global_optimum(Candidate())
    high=restricted_global_optimum(Candidate(switch_per_i2_j_per_a2=.015))
    assert high['selected_q_global']<base['selected_q_global']


def test_fail_closed_current_limit_unfeasible():
    with pytest.raises(ValueError): restricted_global_optimum(Candidate(current_limit_a=1.))
