"""Adversarial tests of an assumed bidirectional converter cost class, not V2 validation."""
import math
from dataclasses import replace
import pytest
from v2_omega_semiconductor_loss_and_identification import ReverseBridge,evaluate,sensitivity,magnetic_waveform
from v2_omega_smooth_storage_metrology_maxcut import Plant

@pytest.fixture(scope='module')
def sample():return evaluate()

def test_signed_gain_exact(sample):
    x=sample
    assert abs(x['ordinary_reverse_loss_w']-x['enhanced_reverse_loss_w']-x['controller_extra_w']-x['recovery_gain_over_ordinary_w'])<1e-12
    assert abs(x['enhanced_bus_w']-x['ordinary_bus_w']-x['recovery_gain_over_ordinary_w'])<1e-12
    assert abs(x['signed_gain_ledger_residual_w'])<1e-12

def test_match_shaft_and_sampled_cycle(sample):
    assert math.isclose(sample['shaft_w'],45,abs_tol=1e-7)
    assert sample['sampled_bus_energy_endpoint_residual_j']==pytest.approx(0,abs=1e-9)
    assert sample['sampled_bus_range_pass']
    assert sample['conditional_design_budget_pass']

def test_not_hardware_proof(sample):
    assert sample['source_selected'] is False
    assert len(sample['missing'])>=3
    assert 'invented' in sample['scope'].lower()

@pytest.mark.parametrize('q,lead',[(0,-.25),(0,-.2),(0,-.15),(.1,-.15),(.2,-.1)])
def test_reconstruct_smooth_coil_port(q,lead):
    w=magnetic_waveform(Plant(n=1024),q,lead)
    assert w['reference']['shaft_w']==pytest.approx(45,abs=1e-7)
    assert w['reference']['gross_reverse_w']>0
    assert w['reference']['gross_forward_w']>0

@pytest.mark.parametrize('key,val',[('r_path_ohm',-.1),('switch_e0_j',-.01),('gate_charge_c',-.1),('controller_extra_w',-1),('deadtime_s',.1),('pwm_hz',0),('active_devices',0)])
def test_reject_invalid_parameters(key,val):
    with pytest.raises(ValueError):evaluate(replace(ReverseBridge(),**{key:val}),Plant(n=512))

@pytest.mark.parametrize('key,val',[('r_path_ohm',.10),('switch_e0_j',.001),('gate_charge_c',2e-6),('deadtime_s',10e-6),('controller_extra_w',10.)])
def test_losses_are_nonnegative_and_monotonic(key,val,sample):
    alt=evaluate(replace(ReverseBridge(),**{key:val}),Plant(n=8192))
    assert alt['recovery_gain_over_ordinary_w']<=sample['recovery_gain_over_ordinary_w']+1e-8
    assert alt['implied_enhanced_reverse_eta']<=1
    assert alt['signed_gain_ledger_residual_w']==pytest.approx(0,abs=1e-9)

@pytest.mark.parametrize('eta',[.9,.95,.99,1.])
def test_ordinary_baseline_already_recovers(eta):
    p=evaluate(ordinary_eta=eta,plant=Plant(n=512))
    assert p['ordinary_reverse_loss_w']==pytest.approx((1-eta)*p['gross_reverse_w'],abs=1e-12)
    assert p['recovery_gain_over_ordinary_w']==pytest.approx(p['ordinary_reverse_loss_w']-p['enhanced_reverse_loss_w']-p['controller_extra_w'],abs=1e-12)

def test_controller_can_reverse_benefit():
    p=evaluate(replace(ReverseBridge(),controller_extra_w=10))
    assert p['recovery_gain_over_ordinary_w']<0
    assert not p['conditional_design_budget_pass']

def test_hard_switch_can_reverse_benefit():
    p=evaluate(replace(ReverseBridge(),switch_e0_j=.001))
    assert p['recovery_gain_over_ordinary_w']<0
    assert not p['conditional_design_budget_pass']

def test_thermal_failure_is_distinct():
    p=evaluate(replace(ReverseBridge(),r_path_ohm=3.0))
    assert p['junction_temperature_c_lumped_upper']>110
    assert not p['thermal_bound_pass']

def test_voltage_failure_is_sufficient_not_necessary():
    p=evaluate(max_required_voltage_extra_v=10)
    assert not p['voltage_bound_pass']
    assert p['conservative_winding_voltage_headroom_v']<0

def test_per_channel_gate_drive_and_deadtime():
    a=evaluate()
    b=evaluate(replace(ReverseBridge(),gate_charge_c=70e-9))
    assert b['gate_driver_w']==pytest.approx(2*a['gate_driver_w'])
    assert b['junction_temperature_c_lumped_upper']==pytest.approx(a['junction_temperature_c_lumped_upper'])

@pytest.mark.parametrize('pwm_hz',[10000,20000,40000])
def test_frequency_scaling(pwm_hz):
    x=evaluate(replace(ReverseBridge(),pwm_hz=pwm_hz),Plant(n=512))
    assert x['switching_loss_w']>0
    assert x['gate_driver_w']==pytest.approx(pwm_hz*2*35e-9*12)

def test_model_is_not_optimized_against_itself():
    # The ordinary path carries a fixed previously calibrated conventional eta;
    # this is a conditional economics comparison, not end-to-end converter proof.
    a=sensitivity()
    assert a['controller_10W']['recovery_gain_over_ordinary_w']<0
    assert a['hard_switch_1mJ']['recovery_gain_over_ordinary_w']<0
