import importlib.util
from pathlib import Path
from fractions import Fraction
import math
import numpy as np
import pytest

SCRIPT=Path(__file__).resolve().parents[1]/'scripts'/'v2_distributed_causal_line_maxcut.py'
spec=importlib.util.spec_from_file_location('line_cut',SCRIPT)
mod=importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)


def test_exact_telegrapher_and_wave_power():
    assert mod.telegrapher_identity()['symbolic_residual']=='0'

def test_fraction_exact_passive_scattering():
    assert mod.exact_fraction_certificate()['energy_balance_residual']=='0'

@pytest.mark.parametrize('bad',[-3,0,1.00001*mod.C0,math.inf])
def test_front_speed_invalid(bad):
    with pytest.raises(ValueError):mod.CausalLine(front_speed_m_s=bad).validate()

@pytest.mark.parametrize('bad',[-1.01,1.01])
def test_load_reflect_invalid(bad):
    with pytest.raises(ValueError):mod.CausalLine(load_reflection=bad).validate()

def test_source_reflect_invalid():
    with pytest.raises(ValueError):mod.CausalLine(source_reflection=2).validate()

def test_amplifier_disallowed():
    with pytest.raises(ValueError):mod.CausalLine(amplitude_survival_per_tick=1.01).validate()

def test_negative_time_or_empty_data_rejected():
    with pytest.raises(ValueError): mod.traveling_packets(mod.CausalLine(),[],7)
    with pytest.raises(ValueError): mod.traveling_packets(mod.CausalLine(),[1],0)

@pytest.mark.parametrize('cells',[1,2,7,13])
def test_strict_no_early_arrival(cells):
    a=[1]+[0]*(cells*3)
    out=mod.traveling_packets(mod.CausalLine(),a,cells)
    assert out['first_forward_arrival_tick']==cells
    assert all(r['forward_arrival']==0 for r in out['trace'][:cells])
    assert out['trace'][cells]['forward_arrival']==1
    assert abs(out['energy_residual_j'])<1e-20

@pytest.mark.parametrize('load_ref,source_ref,atten',[(-1,0,1),(1,0,1),(.4,-.3,.9),(0,0,.5),(1,1,1)])
def test_energy_passivity_both_reflections(load_ref,source_ref,atten):
    line=mod.CausalLine(load_reflection=load_ref,source_reflection=source_ref,
                        amplitude_survival_per_tick=atten)
    a=[.5,-1.5,.1]+[0.]*55
    out=mod.traveling_packets(line,a,7)
    assert out['max_tick_residual_j']<2e-20
    assert abs(out['energy_residual_j'])<2e-19
    assert out['load_work_j']>=-1e-21
    assert out['dissipated_work_j']>=-1e-21
    assert out['source_work_j']>=-1e-20


def test_all_energy_remains_stored_before_arrival():
    l=mod.CausalLine()
    out=mod.traveling_packets(l,[1]+[0]*8,8)
    assert out['trace'][0]['stored_energy_j']>0
    assert all(t['load_energy_j']==0 for t in out['trace'][:8])
    assert out['trace'][8]['load_energy_j']>0


def test_matched_line_is_exact_shift():
    a=[1.,2.,-3.,4.]+[0.]*12
    out=mod.traveling_packets(mod.CausalLine(),a,3)
    assert [t['forward_arrival'] for t in out['trace']][3:3+len(a)-3]==a[:-3]


def test_clock_quantization_is_not_silently_rounded():
    line=mod.CausalLine()
    with pytest.raises(ValueError):mod.traveling_packets(line,[1],10,dt_s=1.0)


def test_bound_smooth_sinusoid():
    dt=1e-9;t=np.arange(2000)*dt
    v=3*np.sin(2*np.pi*2e6*t)
    b=mod.smooth_delay_error_bound(v,dt,9,50)
    assert b['amplitude_max_observed_v'] <= b['amplitude_bound_v']
    assert b['power_max_observed_w'] <= b['power_bound_w']


def test_bound_sharp_monotone_ramp():
    a=np.arange(50)*.002
    b=mod.smooth_delay_error_bound(a,1e-9,5,50)
    assert b['amplitude_max_observed_v'] == pytest.approx(.01)
    assert b['amplitude_bound_v'] == pytest.approx(.01)


def test_edge_warning_in_comparison():
    t=mod.causal_clock_scales()
    assert 2e-9 < t['flight_s'] < 3e-9
    assert t['delay_over_switch_edge']>1
    assert t['carrier_phase_rad']<.001


def test_run_produces_receipt():
    assert abs(mod.run()['reflected_lossy_line']['energy_residual_j'])<1e-21