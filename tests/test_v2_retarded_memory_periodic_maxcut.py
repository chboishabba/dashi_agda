"""Source-independent, numerical/symbolic tests of memory + causal feedback."""
from __future__ import annotations
import importlib.util
from pathlib import Path
from dataclasses import replace
import math
import sys
import numpy as np
import pytest

SRC=Path(__file__).resolve().parents[1]/'scripts'/'v2_retarded_memory_periodic_maxcut.py'
spec=importlib.util.spec_from_file_location('v2memory',SRC)
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)


@pytest.mark.parametrize('phases',range(3,13))
def test_memory_periodic_stability_and_delay_front(phases):
    p=mod.MemoryMachine(phases=phases)
    gate=mod.memory_small_gain(p)
    assert gate['certified']
    assert p.total_delay_s>p.light_delay_s>=p.cable_m/mod.C0
    assert gate['instantaneous_margin_per_s']>gate['delayed_gain_per_s']>0
    eta=gate['history_decay_rate_per_s']
    assert 0<eta<gate['instantaneous_margin_per_s']
    assert abs(eta+gate['delayed_gain_per_s']*math.exp(eta*p.total_delay_s)-gate['instantaneous_margin_per_s'])<1e-9
    assert abs(gate['flux_damping_a']-gate['memory_cross_b']/gate['weight_rho']-(gate['memory_damping_d']-gate['weight_rho']*gate['flux_cross_c']))<1e-9
    assert mod.voltage_bound(p)['delayed_controller_base_voltage_feasible']


@pytest.mark.parametrize('phases',range(3,13))
def test_constructed_saturating_memory_periodic_energy(phases):
    p=mod.MemoryMachine(phases=phases)
    r=mod.periodic_ledger(p,samples=1024)
    assert r['power_balance_max_abs_w']<2e-10
    assert abs(r['cyclic_energy_derivative_w'])<1e-8
    assert abs(r['endpoint_storage_difference_j'])<1e-11
    assert r['memory_dissipation_w']>0
    assert r['copper_loss_w']>0
    assert r['generator_shaft_extraction_w']>0
    assert r['exported_terminal_power_w']>0
    assert abs(r['generator_shaft_extraction_w']-(r['exported_terminal_power_w']+r['copper_loss_w']+r['memory_dissipation_w']))<1e-8
    assert abs(r['source_base_power_w']+r['delayed_active_controller_work_w']-r['terminal_power_w'])<1e-10
    assert r['observed_voltage_max_v']<=r['voltage_analytic']['terminal_voltage_component_v']+1e-11
    assert r['observed_base_max_v']<=r['voltage_analytic']['base_source_voltage_component_v']+1e-11


def test_exact_twowinding_symbolic_memory_identity():
    s=mod.exact_two_winding_memory_identity()
    assert s['sympy_residual']=='0'
    assert s['two_windings']


@pytest.mark.parametrize('phases',(3,6,9))
def test_actual_delayed_history_matches_analytic_envelope(phases):
    p=mod.MemoryMachine(phases=phases)
    r=mod.integrate_delayed_history(p,cycles=2,steps_per_delay=5)
    assert r['step_is_shorter_than_delay']
    assert r['pointwise_bounds_numerically_satisfied']
    assert r['observed_final_weighted_error']<r['analytic_final_bound']


@pytest.mark.parametrize('phases',(3,5,9))
def test_active_source_is_never_free_recovery(phases):
    p=mod.MemoryMachine(phases=phases)
    r=mod.periodic_ledger(p,512)
    assert abs(r['delayed_active_controller_work_w'])>0.001
    assert abs(r['source_base_power_w']+r['delayed_active_controller_work_w']-r['terminal_power_w'])<1e-10


@pytest.mark.parametrize('gain',(.5,1.,-1.,10.))
def test_sufficient_gain_condition_fails_closed(gain):
    gate=mod.memory_small_gain(mod.MemoryMachine(feedback_gain_ohm=gain))
    assert not gate['certified']
    assert gate['history_decay_rate_per_s'] is None
    # No claim of actual instability follows from failure of this sufficient test.


@pytest.mark.parametrize('overrides',[
    dict(ell=-1.), # not a dataclass parameter, caught as invalid construction
    dict(base_h=.01),dict(saturating_h=-.001),dict(saturation_a=0.),
    dict(resistance_ohm=0.),dict(coupling_g=-.003),dict(memory_h=1e-5),
    dict(mobility=0.),dict(cable_m=0.),dict(front_m_s=mod.C0*1.001),
    dict(front_m_s=0.),dict(processing_latency_s=-.01),dict(current_dc_a=0.,current_ac_a=.6),
    dict(phases=2),dict(voltage_limit_v=0.),dict(feedback_gain_ohm=float('nan')),
])
def test_invalid_material_or_superluminal_parameters_rejected(overrides):
    if 'ell' in overrides:
        with pytest.raises(TypeError):mod.MemoryMachine(**overrides)
    else:
        with pytest.raises(ValueError):mod.MemoryMachine(**overrides).check()


def test_fixed_bus_negative_control():
    p=mod.MemoryMachine(voltage_limit_v=2.)
    assert not mod.voltage_bound(p)['continuous_voltage_feasible']


def test_high_memory_gain_uncertified_not_observed_instability():
    p=mod.MemoryMachine(coupling_g=.008,memory_h=.004)
    gate=mod.memory_small_gain(p)
    assert not gate['certified']


def test_passive_memory_approaches_prior_model_as_coupling_vanishes():
    p=mod.MemoryMachine(coupling_g=0,feedback_gain_ohm=0)
    gate=mod.memory_small_gain(p)
    assert gate['certified']
    assert gate['delayed_gain_per_s']==0
    assert math.isclose(gate['history_decay_rate_per_s'],min(p.resistance_ohm/p.Lambda,p.mobility*p.memory_h))


def test_genuine_delay_retained_without_processing_latency():
    p=mod.MemoryMachine(processing_latency_s=0)
    assert p.total_delay_s==p.light_delay_s
    assert p.total_delay_s>=p.cable_m/mod.C0
    assert mod.memory_small_gain(p)['certified']


def test_inverse_flux_adversarial_randomised_multiphase():
    rng=np.random.default_rng(29)
    for m in (3,6,9):
        p=mod.MemoryMachine(phases=m)
        for _ in range(6):
            t=float(rng.uniform(-p.cycle_s,p.cycle_s))
            i=rng.uniform(-4,4,m)
            z=rng.uniform(-1,1,m)
            flux,*_=mod.constitutive(p,t,i,z)
            found=mod.inverse_flux(p,t,flux,z,np.zeros(m))
            assert np.max(np.abs(found-i))<1e-9


def test_reference_lag_is_actual_passive_memory_solution():
    for m in (3,6,9):
        p=mod.MemoryMachine(phases=m)
        for t in np.linspace(0,p.cycle_s,40):
            i,di,z,dz=mod.reference(p,float(t))
            h=1e-6
            zf=mod.reference(p,float(t+h))[2]
            zb=mod.reference(p,float(t-h))[2]
            assert np.max(np.abs((zf-zb)/(2*h)-dz))<1e-5
            assert np.max(np.abs(dz-p.mobility*(p.coupling_g*i-p.memory_h*z)))<1e-11


def test_same_signed_boundary_composition_with_negative_motor_port():
    x=mod.conditional_telegrapher_machine_port_weld()
    assert x['exact_symbolic_residual']=='0'
    assert x['exact_fraction_composed_residual']=='0'
    assert x['signed_motor_port_j']=='-2'
    assert 'prior passive-resistor' in x['motor_negative_port_is_active']
    assert 'UNVERIFIED' not in x['strict_unclosed']
