"""Independent deterministic tests; not V2 hardware experiments."""
import importlib.util
from pathlib import Path
from dataclasses import replace

import pytest

SCRIPT=Path(__file__).resolve().parents[1]/'scripts/check_reluctance_permeance_phase_maxcut.py'
spec=importlib.util.spec_from_file_location('reluctance_phase',SCRIPT)
m=importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name]=m
spec.loader.exec_module(m)


def test_symbolic_identity_all_three_models():
    r=m.coenergy_symbolic_certificate()
    assert r['linear_electromechanical_port_identity']=='symbolically zero'
    assert r['nonlinear_saturating_coenergy_port_identity']=='symbolically zero'
    assert r['symmetric_mutual_inductance_port_identity']=='symbolically zero'


def test_3_6_9_and_adversarial_nonmultiple_optima():
    r=m.ideal_phase_optimisations()
    w=r['winners']
    assert w['0.150']['phase_count']==3
    assert w['0.015']['phase_count']==6
    assert w['0.005']['phase_count']==9
    assert w['0.030']['phase_count']==5
    assert w['0.010']['phase_count']==7


def test_all_phases_cover_sensitivity_and_limit():
    a=[m.ideal_phase_cover(n) for n in range(3,13)]
    assert all(0<x['worst_sensitivity']<1 for x in a)
    assert all(a[k]['worst_sensitivity'] < a[k+1]['worst_sensitivity'] for k in range(len(a)-1))
    assert all(a[k]['constant_torque_current_sq_multiplier'] > a[k+1]['constant_torque_current_sq_multiplier'] for k in range(len(a)-1))
    assert a[0]['worst_sensitivity']==pytest.approx(0.5)
    with pytest.raises(ValueError):m.ideal_phase_cover(2)


@pytest.mark.parametrize('n', [3,4,5,6,7,8,9,10,11,12])
def test_synthetic_pulse_power_closes(n):
    x=m.simulate(n,0.,1.5,m.Model())
    assert x['max_sample_port_residual_w']<1e-8
    assert abs(x['mean_storage_derivative_w'])<1e-4
    assert abs(x['copper_w']-10.5)<1e-7
    assert x['ideal_net_electrical_out_w'] < x['mean_electromagnetic_braking_w']
    assert x['realistic_bus_out_w'] < x['ideal_net_electrical_out_w']


def test_lossless_upper_bound_is_not_extra_energy():
    mdl=replace(m.Model(), R_ohm=0., eta_forward=1., eta_reverse=1.,switch_overhead_w_per_phase=0.)
    r=m.simulate(6,0.,1.5,mdl)
    assert r['ideal_net_electrical_out_w']==pytest.approx(r['mean_electromagnetic_braking_w'],abs=1e-8)
    assert r['realistic_bus_out_w']==pytest.approx(r['mean_electromagnetic_braking_w'],abs=1e-8)


def test_converter_efficiency_monotonic():
    a=m.simulate(6,0.,1.5,m.Model())
    b=m.simulate(6,0.,1.5,replace(m.Model(),eta_forward=1.,eta_reverse=1.))
    assert b['realistic_bus_out_w']>a['realistic_bus_out_w']


def test_voltage_and_torque_trades():
    r=m.optimize_pulses(m.Model())['per_phase_count']
    assert [v['phases'] for v in r]==list(range(3,13))
    assert all(v['peak_terminal_voltage_v']<=250.0001 for v in r)
    assert all(v['high_resolution_voltage_pass'] for v in r)
    assert all(abs(v['8x_power_difference_w'])<.001 for v in r)
    assert r[0]['torque_ripple_rms_over_mean'] > r[3]['torque_ripple_rms_over_mean']
    assert r[3]['torque_ripple_rms_over_mean'] > r[6]['torque_ripple_rms_over_mean']
    assert r[0]['realistic_bus_out_w'] > r[6]['realistic_bus_out_w']


def test_impossible_geometry_guard():
    with pytest.raises(ValueError):m.simulate(3,0.,1.5,replace(m.Model(), L_mean_h=.001))


def test_attribution_is_explicit():
    source=SCRIPT.read_text()
    assert "'not_a_device_calibration':True" in source
    assert "'not_attributed_to_v2'" in source