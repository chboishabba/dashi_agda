import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import pytest
from v2_omega_robust_pulse_recovery import Uncertainty,point,run

@pytest.fixture(scope='module')
def baseline():return run()

def test_nominal_lead_zero_loses_robust_certificate(baseline):
    p=baseline['nominal_q0_lead0']
    assert p['minimum_voltage_headroom_v']<0
    assert not p['corner_robust_winding_bus_certified']

def test_optimized_lead_recovers_robust_margin(baseline):
    best=baseline['winner']
    assert best is not None
    assert best['minimum_voltage_headroom_v']>=0
    assert best['minimum_correlated_recovery_gain_lower_w']>0

def test_matched_shaft_and_storage(baseline):
    for corner in baseline['winner']['corners']:
        assert abs(corner['shaft_w']-45)<1e-7
        assert corner['full_cycle_storage_by_manufactured_waveform']
        assert corner['continuous_bus_enclosure_certified']

def test_uncertainty_breaks_strongly_derated_certificate():
    p=point(0.,-.2,Uncertainty(voltage_derating_v=25.),n=4096)
    assert not p['corner_robust_winding_bus_certified']

def test_high_controller_overhead_kills_gain():
    p=point(0.,-.2,Uncertainty(added_controller_overhead_max_w=12.),n=4096)
    assert p['minimum_correlated_recovery_gain_lower_w']<0
    assert not p['corner_robust_winding_bus_certified']

def test_worse_converter_no_guaranteed_gain():
    p=point(0.,-.2,Uncertainty(enhanced_eta_min=.94,ordinary_eta_max=.955),n=4096)
    assert p['minimum_correlated_recovery_gain_lower_w']<0

def test_uncertainty_validation():
    with pytest.raises(ValueError):Uncertainty(voltage_derating_v=-1).validate()
    with pytest.raises(ValueError):Uncertainty(enhanced_eta_min=1.01).validate()

def test_finite_enumeration_not_global(baseline):
    assert baseline['candidates']==30
    assert baseline['robust_certified_count']>0
    assert not baseline['source_identified']
    assert not baseline['measured_V2_efficiency']

def test_corner_voltage_gain_monotonic_under_R():
    p=point(0.,-.15,n=4096)
    by_R={r:[] for r in (0.,.03)}
    for c in p['corners']:by_R[c['resistance_increase_ohm']].append(c['required_voltage_upper_v'])
    assert min(by_R[.03])>=max(by_R[0.])
