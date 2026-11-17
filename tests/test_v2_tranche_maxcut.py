import sys
from pathlib import Path
from dataclasses import replace
import math
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from v2_source_bounded_efficiency_maxcut import Machine, arm, comparison, q_limit
import v2_tranche_maxcut as t

@pytest.fixture(scope='module')
def res(): return t.run(29)

@pytest.mark.parametrize('n',[5,17,29])
def test_disjoint_producers_shape(n):
    r=t.run(n)['tranches'];assert len(r['AB']['rows'])==n
    assert len(r['CD']['rows'])==2*n
    assert r['G']['number_of_candidates']==2*n
    assert len(r['EF']['rows'])==12

def test_mechanical_match_and_mass_ledger(res):
    for arm in res['tranches']['AB']['rows']:
        assert math.isclose(arm['mechanical_input_w'],45,abs_tol=1e-8)
        assert arm['peak_current_a']<=8+1e-8
        assert arm['storage_delta_j_per_rev']==0
    for case in res['tranches']['CD']['rows']:
        assert math.isclose(case['bus_w']+case['total_losses_w'],45,abs_tol=1e-8)
        assert case['clamp_recovered_w']<=case['clamp_available_w']+1e-8

def test_ordinary_not_artificial_dumper():
    c=t.tranche_cd(Machine(),t.Contract(),7)
    baseline=next(x for x in c['rows'] if x['q']==0 and not x['recovery'])
    assert baseline['clamp_recovered_w']>0
    assert baseline['clamp_recovered_w']<baseline['clamp_available_w']

def test_storage_admission_separation(res):
    for r in res['tranches']['G']['finite_grid_pareto']:
        assert r['initial_final_winding_storage_matched']
        assert not r['whole_system_stationarity_certified']
        assert not r['finite_voltage_slew_certified']

def test_finite_dominance_exact(res):
    assert all(not any(t._dominates(y,x) for y in res['tranches']['G']['finite_grid_pareto'] if y is not x)
               for x in res['tranches']['G']['finite_grid_pareto'])
    assert res['tranches']['G']['best_grid_candidate']['bus_w'] <= 45

def test_converter_stress_negative_control(res):
    g=res['tranches']['G'];assert g['negative_controls']['very_high_controller_overhead_bus_w']<g['ordinary_bus_w']
    assert g['negative_controls']['poor_recovery_bus_w']<g['ordinary_bus_w']

def test_eta_motor_bound():
    with pytest.raises(ValueError): t.drivetrain(45,.5,40,20)
    with pytest.raises(ValueError): t.drivetrain(40,.9,45,20)
    with pytest.raises(ValueError): t.drivetrain(286,.8,45,46)

@pytest.mark.parametrize('eta',[.3,.45,.8,.95])
def test_full_drivetrain_no_shaft_doublecount(eta):
    x=t.drivetrain(286,eta,45,22)
    assert abs(x['full_boundary_residual_w'])<1e-8
    assert math.isclose(x['motor_internal_loss_w'],286*(1-eta))
    assert math.isclose(x['motor_shaft_w'],286*eta)

def test_h_nonidentifiable_worlds(res):
    h=res['tranches']['H']; assert h['cannot_source_infer']
    assert h['required_loss_delta_if_complete_meter_and_stationary_w']==[-47.,-45.,-43.]
    assert len(h['indistinguishable_conservation_worlds']['worlds'])>=4
    assert all(w['closed_residual_w']==0 for w in h['indistinguishable_conservation_worlds']['worlds'].values())

@pytest.mark.parametrize('shaft',[20.,45.,60.])
def test_common_shaft_perturbation(shaft):
    m=replace(Machine(),shaft_power_w=shaft)
    c=replace(t.Contract(),shaft_w=shaft)
    try:
        s=t.tranche_cd(m,c,9)
    except ValueError:
        # Valid rejection when cap cannot supply requested shaft at any q.
        assert shaft>=45
    else:
        assert all(math.isclose(r['bus_w']+r['total_losses_w'],shaft,abs_tol=1e-7) for r in s['rows'])

@pytest.mark.parametrize('negative_eta',[0.,-1.,1.1])
def test_invalid_motor_eta(negative_eta):
    with pytest.raises(ValueError):t.drivetrain(286,negative_eta,45,20)

def test_sensitivity_stress():
    z=t.sensitivity_scenarios(Machine(),t.Contract())
    assert len(z['cases'])==18
    assert z['positive_combined']>0 and z['negative_combined']>0

def test_full_model_default_45_not_claimed(res):
    assert res['omega']['status'].startswith('PARTIAL')
    assert res['tranches']['H']['cannot_source_infer']

def test_equal_meter_not_equal_shaft():
    w=t.equal_input_variable_motor_efficiency()
    assert abs(w['shaft_delta_w']-45)<1e-12
    assert abs(w['motor_loss_reduction_w']-45)<1e-12
    assert math.isclose(w['eta_after']-.6,45/286)
    with pytest.raises(ValueError):t.equal_input_variable_motor_efficiency(initial_efficiency=.95)
