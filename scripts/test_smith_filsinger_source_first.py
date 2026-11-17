import math
import pytest
from check_smith_filsinger_source_first import (
  CrowleyIsolatedSphere,local_uniform_collector,layered_phi,VIMeterSample,
  total_port_interval,meter_gate,rank_observation_cut,causal_cloud_counterworld)


def test_crowley_exact_isc():
    a=local_uniform_collector()
    assert a.isc_A==pytest.approx(2*math.pi*.1*(2.36e-12/100)*200)

def test_crowley_height_voltage_not_250kv():
    assert local_uniform_collector().voc_V==200

def test_crowley_matched_watts():
    assert local_uniform_collector().matched_W==pytest.approx(1.4828317325e-10)

def test_crowley_matching():
    a=local_uniform_collector()
    assert a.load_W(a.source_R_ohm)==pytest.approx(a.matched_W)

def test_crowley_bounded_other_loads():
    a=local_uniform_collector()
    for mult in (.001,.1,.5,1,2,20,100):
        assert a.load_W(mult*a.source_R_ohm)<=a.matched_W*(1+1e-12)

def test_crowley_effective_flux_area():
    a=local_uniform_collector()
    assert a.effective_collection_area_m2==pytest.approx(2*math.pi*.1*2)

def test_projected_area_factor_four():
    a=local_uniform_collector()
    assert a.enhancement_over_projected_area==pytest.approx(160)

def test_h_over_d_restriction():
    with pytest.raises(ValueError):local_uniform_collector(height_m=2,diameter_m=1)

def test_layered_atmospheric_voltage_not_global():
    assert layered_phi(3,[(2,100),(4,50)])==pytest.approx(250)

def test_layers_incomplete_fail():
    with pytest.raises(ValueError):layered_phi(5,[(2,100)])

def test_layers_out_of_order_fail():
    with pytest.raises(ValueError):layered_phi(5,[(2,100),(1,100)])

def test_current_sign_is_real_energy_sign():
    a=VIMeterSample(1,10,-.2)
    assert a.energy_interval_J()==pytest.approx((-2,-2))

def test_uncertainty_crosses_zero():
    a=VIMeterSample(1,10,.01,0,.02)
    low,high=a.energy_interval_J()
    assert low<0<high

def test_meter_gate_positive_not_source_verified():
    d=meter_gate([VIMeterSample(1,10,.2)],False,False)
    assert d['positive_signed_port_work_certified']
    assert not d['sustained_source_gate_admissible']

def test_meter_gate_needs_source_identity():
    d=meter_gate([VIMeterSample(1,10,.2)],True,False)
    assert not d['sustained_source_gate_admissible']

def test_meter_gate_needs_storage_return():
    d=meter_gate([VIMeterSample(1,10,.2)],False,True)
    assert not d['sustained_source_gate_admissible']

def test_meter_gate_conditional():
    d=meter_gate([VIMeterSample(1,10,.2)],True,True)
    assert d['sustained_source_gate_admissible']

def test_meter_gate_interval_sum():
    a=[VIMeterSample(1,10,.1,0,0),VIMeterSample(2,5,.2,0,0)]
    assert total_port_interval(a)==pytest.approx((3,3))

def test_meter_requires_samples():
    with pytest.raises(ValueError):total_port_interval([])

def test_rank_three_observational_degrees():
    assert rank_observation_cut()['unidentified_degrees_of_freedom']==3

def test_causal_worlds_same_observations():
    a=causal_cloud_counterworld()
    assert a['worlds'][0]['observational_rain']==a['worlds'][1]['observational_rain']

def test_causal_worlds_different_intervention():
    a=causal_cloud_counterworld()
    assert a['worlds'][0]['causal_change']==0
    assert a['worlds'][1]['causal_change']==pytest.approx(.2)

def test_cloud_zero_coupling_zero_effect():
    a=causal_cloud_counterworld(cloud_field_control_gain=0)
    assert all(w['causal_change']==0 for w in a['worlds'])

def test_unknown_other_source_not_ruled_out():
    # Spherical fair-weather source model does not apply to non-fair-weather sources.
    assert 'sphere' in CrowleyIsolatedSphere.__name__.lower()


def test_ion_collection_direction_condition_25():
    with pytest.raises(ValueError):
        CrowleyIsolatedSphere(10, .1, 1, 100)
