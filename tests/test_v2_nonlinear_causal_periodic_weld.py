"""Adversarial acceptance for nonlinear periodic flux-state contraction.

Results are source-independent exact analytical bounds instantiated and
numerically cross-checked; not numerical proof of a physical V2 machine.
"""
import importlib.util
import math
from pathlib import Path
from dataclasses import replace

import numpy as np
import pytest

SRC=Path(__file__).resolve().parents[1]/'scripts'/'v2_nonlinear_causal_periodic_weld.py'
spec=importlib.util.spec_from_file_location('v2periodicnonlinear',SRC)
mod=importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)

@pytest.mark.parametrize('m',range(3,13))
def test_spd_and_analytic_voltage_at_all_phases(m):
    p=mod.Parameters(phases=m)
    b=mod.analytic_bounds(p)
    assert b['min_incremental_inductance_h']>0
    assert b['bus_voltage_feasible']
    assert 0<b['cycle_contraction']<1
    for t in np.linspace(0,p.period,32):
        i,di,ddi=mod.target(p,float(t))
        psi,H,U,tau,Ldot=mod.constitutive(p,float(t),i)
        ev=np.linalg.eigvalsh(H)
        assert ev[0]>=p.lower-1e-12
        assert ev[-1]<=p.upper+1e-12
        assert np.max(np.abs(i))<=b['current_component_envelope_a']+1e-12
        assert np.max(np.abs(di))<=b['current_slew_component_envelope_a_per_s']+1e-10
        assert np.max(np.abs(mod.commanded_voltage(p,float(t))))<=b['commanded_voltage_component_bound_v']+1e-10
        assert U>=0

@pytest.mark.parametrize('m',(3,4,5,6,7,8,9,10,11,12))
def test_nonlinear_mutual_ledger_and_no_storage_drain(m):
    p=mod.Parameters(phases=m)
    row=mod.energy_cycle(p,samples=1024)
    assert row['nonlinear_and_mutually_coupled']
    assert row['pointwise_energy_residual_max_w']<1e-10
    assert abs(row['average_energy_derivative_w'])<1e-10
    assert abs(row['average_terminal_input_w']+row['ideal_bus_export_w'])<1e-10
    assert row['shaft_extraction_w']>row['copper_w']>0
    assert row['measured_peak_voltage_v']<=row['analytic_voltage_upper_v']+1e-10

@pytest.mark.parametrize('m',(3,6,9))
def test_attractor_after_one_and_three_cycles(m):
    p=mod.Parameters(phases=m)
    a=mod.solve_perturbation(p,cycles=1)
    b=mod.solve_perturbation(p,cycles=3)
    assert a['contraction_verified']
    assert b['contraction_verified']
    assert b['final_flux_error_norm_wb']<a['final_flux_error_norm_wb']
    assert b['analytic_error_upper_wb']<a['analytic_error_upper_wb']

@pytest.mark.parametrize('m',(3,6,9))
def test_causal_delay_forced_contraction_with_same_initial(m):
    p=mod.Parameters(phases=m)
    obs=mod.solve_perturbation(p,cycles=2,delay=p.delay_s)
    assert obs['contraction_verified']
    assert obs['final_flux_error_norm_wb']<=obs['analytic_error_upper_wb']
    assert p.delay_s>=p.cable_m/mod.C0


def test_delay_bound_and_step_negative_control():
    p=mod.Parameters()
    b=mod.analytic_bounds(p)
    assert b['delayed_drive_difference_2norm_bound_v']>0
    assert b['nonlinear_current_error_ultimate_2norm_a']>0
    assert b['nonlinear_flux_error_ultimate_2norm_wb']>0
    edge=mod.switching_edge_negative_control(p)
    assert edge['instantaneous_difference_v']==100.
    assert edge['remotely_received_step_at_t']==0.
    assert edge['violation_of_smooth_lipschitz_assumption']


def test_precomputed_phase_lead_not_new_information():
    p=mod.Parameters()
    for t in (.1,.2,1.):
        x=mod.delayed_source_precompensation(p,t)
        assert np.max(np.abs(x['transmitted_voltage']-x['source_wave_at_launch']))<1e-12
        assert x['source_launch_time']<x['at_load_time']
        assert 'preprogrammed' in x['assumption']

@pytest.mark.parametrize('changes',[
    dict(base_h=.01), dict(saturation_h=-.1), dict(saturation_a=0),
    dict(wavefront_speed_m_s=1.01*mod.C0),dict(wavefront_speed_m_s=0.),
    dict(bus_v=0.),dict(i0_a=.2,i1_a=.3),dict(phases=2),dict(r_ohm=0.)])
def test_reject_nonphysical_or_invalid_data(changes):
    with pytest.raises(ValueError):mod.Parameters(**changes).check()


def test_finite_bus_negative_control():
    p=mod.Parameters(bus_v=3.)
    assert not mod.analytic_bounds(p)['bus_voltage_feasible']


def test_uncoupled_limit_and_nonzero_saturation():
    p=mod.Parameters()
    i,_,_=mod.target(p,0.)
    c=mod.constitutive(p,0.,i)
    q=replace(p,mutual_h=0.,saturation_h=.00001)
    d=mod.constitutive(q,0.,i)
    assert not np.allclose(c[0],d[0])
    assert np.linalg.eigvalsh(c[1])[0]>0


def test_global_result_scope_fail_closed():
    report=mod.run()
    assert len(report['phase_rows'])==10
    assert report['attractor_check']['contraction_verified']
    assert report['delayed_check']['contraction_verified']
    assert any('hysteretic' in g for g in report['open_gates'])
    assert 'NOT actual V2' in report['scope']


@pytest.mark.parametrize('m',(3,4,6,9,12))
def test_nonlinear_retarded_feedback_small_gain_and_exponential_decay(m):
    p=mod.Parameters(phases=m)
    x=mod.delayed_feedback_small_gain(p)
    assert x['frontend_cable_delay_s']>=p.cable_m/mod.C0
    assert x['total_retarded_delay_s']>x['frontend_cable_delay_s']
    assert x['stable_periodic_orbit_certified']
    assert 0<x['exponential_history_convergence_per_s']<x['a_self_dissipation_per_s']
    assert x['periodic_response_contraction']<1.
    eta=x['exponential_history_convergence_per_s']
    assert abs(eta+x['b_delayed_gain_per_s']*math.exp(eta*x['total_retarded_delay_s'])
               -x['a_self_dissipation_per_s'])<1e-9


@pytest.mark.parametrize('m',(3,6,9))
def test_delayed_feedback_source_work_not_free(m):
    p=mod.Parameters(phases=m)
    r=mod.delayed_feedback_periodic_energy(p)
    e=mod.energy_cycle(p,1024)
    assert r['maximum_pointwise_port_balance_error_w']<1e-10
    assert abs(r['base_drive_work_mean_w']+r['external_feedback_work_mean_w']
               -r['total_terminal_work_mean_w'])<1e-9
    assert abs(r['total_terminal_work_mean_w']+e['ideal_bus_export_w'])<1e-9
    assert r['external_feedback_work_mean_w']>0


@pytest.mark.parametrize('gain',(1.0,-1.0,10.))
def test_delayed_feedback_failed_small_gain_does_not_assert_instability(gain):
    x=mod.delayed_feedback_small_gain(mod.Parameters(),gain)
    assert not x['stable_periodic_orbit_certified']
    assert x['exponential_history_convergence_per_s'] is None
    with pytest.raises(ValueError):mod.delayed_feedback_periodic_energy(mod.Parameters(),gain)


def test_zero_retarded_feedback_reduces_to_prior_contraction():
    p=mod.Parameters()
    x=mod.delayed_feedback_small_gain(p,0.)
    assert x['stable_periodic_orbit_certified']
    assert x['exponential_history_convergence_per_s']==p.r_ohm/p.upper
    assert x['periodic_response_contraction']==0.


def test_invalid_controller_latency_rejected():
    with pytest.raises(ValueError):mod.delayed_feedback_small_gain(mod.Parameters(),.25,-1.)
