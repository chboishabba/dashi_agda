import math
import numpy as np
import pytest
from check_v2_pulse_nonlinear_recovery import Candidate,nonlinear_identity,pulse_window,optimize_grid,phase_symmetry_null

def test_nonlinear_coenergy_identity():
    assert nonlinear_identity()['residual']=='0'

def test_phase_count_null():
    assert 'independent' in phase_symmetry_null()['matched_copper']

@pytest.mark.parametrize('q',[0,.1,.25,.5,.7,.8,.9,.95])
def test_closed_energy_account(q):
    v=pulse_window(Candidate(current_limit_a=100),q)
    assert abs(v['complete_balance_residual_w'])<1e-10
    assert v['mechanical_extraction_w']==45

@pytest.mark.parametrize('q',[0,.25,.5,.7,.8,.9])
def test_analytic_sine_integral_matches_quadrature(q):
    t=np.linspace(0,2*np.pi,400000,endpoint=False)
    g=np.sin(t)
    active=g>q
    expected=pulse_window(Candidate(),q)
    assert abs(active.mean()-expected['active_fraction'])<1e-5
    assert abs(np.mean(g*active)-math.sqrt(1-q*q)/math.pi)<1e-5

def test_pulse_selectivity_copper_reduction():
    model=Candidate(current_limit_a=100,switch_fixed_j=0,switch_per_i2_j_per_a2=0)
    a=pulse_window(model,0);b=pulse_window(model,.8)
    assert b['copper_loss_w']<a['copper_loss_w']

def test_nonideal_switching_can_reverse_improvement():
    a=Candidate(current_limit_a=100,switch_per_i2_j_per_a2=.01)
    # More pulse concentration increases switch energy, negating copper gain.
    assert pulse_window(a,.8)['ideal_net_bus_w']<pulse_window(a,0)['ideal_net_bus_w']

def test_grid_feasibility_and_optimum():
    ans=optimize_grid(Candidate())
    assert ans['best']['current_limit_feasible']
    assert ans['improvement_w']>=0
    assert ans['best']['peak_current_a']<=8
    assert ans['feasible_count']>0

def test_unphysical_inputs_rejected():
    with pytest.raises(ValueError):pulse_window(Candidate(),-0.1)
    with pytest.raises(ValueError):pulse_window(Candidate(),1.0)
    with pytest.raises(ValueError):pulse_window(Candidate(l_harmonic_h=.041),0.5)