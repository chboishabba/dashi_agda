import importlib.util, sys, math
from pathlib import Path
import pytest

P=Path(__file__).resolve().parents[1]/'scripts'/'v2_periodic_causal_motor_certificate.py'
s=importlib.util.spec_from_file_location('periodic',P)
m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m)


def test_exact_identity():assert m.phase_exact_identity()['exact_linear_coenergy_identity']=='0'

@pytest.mark.parametrize('phases',list(range(3,13)))
def test_all_phases_have_constructive_periodic_solution(phases):
    r=m.certificate(m.PeriodicModel(),phases)
    assert r['periodic_orbit_unique_attractive']
    assert r['poincare_contraction']<1
    assert r['bus_voltage_feasible_certified']
    assert r['ideal_net_export_w']>0
    assert r['max_pointwise_residual_w']<1e-9
    assert r['minimum_winding_current_a']>=0


def test_three_phase_third_harmonic_ripple():
    r=m.certificate(m.PeriodicModel(),3)
    assert r['predicted_exact_ripple_rms']==pytest.approx(.6/(4*math.sqrt(2)),abs=1e-13)

@pytest.mark.parametrize('phases',[4,5,6,7,8,9,10,11,12])
def test_other_phase_exact_torque_cancel(phases):
    r=m.certificate(m.PeriodicModel(),phases)
    assert r['fractional_torque_ripple_rms']<1e-12


def test_phase_invariance_of_energy_budget():
    rows=[m.certificate(m.PeriodicModel(),n) for n in range(3,13)]
    assert max(r['mean_copper_w'] for r in rows)-min(r['mean_copper_w'] for r in rows)<1e-12
    assert max(r['mean_shaft_extraction_w'] for r in rows)-min(r['mean_shaft_extraction_w'] for r in rows)<1e-12


def test_exact_period_contraction_less_than_one():
    p=m.PeriodicModel()
    assert 0<p.contraction<1
    direct=math.exp(-p.resistance_ohm*p.period_s/math.sqrt(p.l0_h**2-p.harmonic_h**2))
    assert p.contraction==direct


def test_reject_insufficient_voltage():
    p=m.PeriodicModel(bus_voltage_v=.1)
    assert not m.certificate(p,3)['bus_voltage_feasible_certified']


def test_invalid_nonpositive_inductance():
    with pytest.raises(ValueError):m.PeriodicModel(l0_h=.01,harmonic_h=.012).validate()


def test_invalid_negative_current():
    with pytest.raises(ValueError):m.PeriodicModel(i0_a=.2,i1_a=.6).validate()


def test_fixed_rms_optimum_is_boundary_unipolar():
    p=m.PeriodicModel()
    result=m.max_generation_with_fixed_rms(p)
    assert result['optimal_unipolar_i0_a']==result['optimal_unipolar_i1_a']
    assert result['max_mean_mechanical_extraction_w']>0


def test_generated_receipt():
    assert len(m.run()['phase_rows'])==10


def test_sensor_delay_exact_lag_reduces_generation():
    p=m.PeriodicModel()
    r=m.causal_sensor_delay_weld(p,1e-5)
    assert r['uncompensated_generation_w']<.5*p.harmonic_h*p.harmonic*p.omega*p.i0_a*p.i1_a
    assert r['uncompensated_loss_from_lag_w']>0


def test_predictor_uses_only_retarded_measured_state():
    r=m.causal_sensor_delay_weld(m.PeriodicModel(),1e-6)
    assert r['predicted_phase_error_bound_rad']==0


def test_bounded_acceleration_prediction_remainder():
    p=m.PeriodicModel()
    r=m.causal_sensor_delay_weld(p,1e-5,100)
    assert r['predicted_phase_error_bound_rad']==pytest.approx(.5*p.harmonic*100*1e-10)

@pytest.mark.parametrize('bad',[-1.,-1e-5])
def test_invalid_negative_flight_or_acceleration(bad):
    with pytest.raises(ValueError):m.causal_sensor_delay_weld(m.PeriodicModel(),bad)
    with pytest.raises(ValueError):m.causal_sensor_delay_weld(m.PeriodicModel(),1e-9,bad)