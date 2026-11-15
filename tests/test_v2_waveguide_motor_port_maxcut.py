"""Coupled line/memory machine: real bidirectional port, no instantaneous action."""
import importlib.util
from pathlib import Path
import sys
from dataclasses import replace
import numpy as np
import pytest
SRC=Path(__file__).resolve().parents[1]/'scripts'/'v2_waveguide_motor_port_maxcut.py'
spec=importlib.util.spec_from_file_location('v2_port',SRC)
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)


def test_exact_rational_signed_reflection_and_passive_line():
    assert mod.rational_wave_balance()['equal']
    assert mod.rational_lossy_waveguide_step()['exact']
    assert mod.rational_lossy_waveguide_step()['dissipated']!='0'

@pytest.mark.parametrize('m',range(3,13))
def test_dynamic_coupled_multicoil_real_port_passivity(m):
    p=mod.Params(phases=m)
    r=mod.run(p,steps=12)
    assert r['maximum_single_step_residual_j']<2e-11
    assert abs(r['cumulative']['integrated_balance_error_j'])<2e-10
    assert r['cumulative']['copper_loss_j']>0
    assert r['cumulative']['memory_loss_j']>0
    assert r['cumulative']['line_loss_j']>0
    assert r['max_implicit_residual_inf']<2e-9

@pytest.mark.parametrize('cells',(1,2,3,5))
def test_finite_signal_arrival_and_return_round_trip(cells):
    # Simulate two worlds differing only in the launch at tick zero.
    # The remote winding cannot react before cells flight ticks; the
    # source-side detector cannot see its echo before 2*cells ticks.
    p=mod.Params(phases=3,delay_cells=cells,omega_rad_s=0.)
    pulsed=mod.initial(p)
    quiet=mod.initial(p)
    delta_remote=[]
    delta_return=[]
    for k in range(2*cells+3):
        f=np.zeros(p.phases)
        if k==0:f[0]=3.0
        a=mod.step(p,pulsed,f)
        b=mod.step(p,quiet,np.zeros(p.phases))
        delta_remote.append(abs(a['incident'][0]-b['incident'][0]))
        delta_return.append(abs(a['returned_source'][0]-b['returned_source'][0]))
        pulsed,quiet=a['state'],b['state']
    assert all(x<1e-14 for x in delta_remote[:cells])
    assert delta_remote[cells]>0
    assert all(x<1e-14 for x in delta_return[:2*cells])
    assert delta_return[2*cells]>0

@pytest.mark.parametrize('eta',(0.,0.5,.8,1.))
def test_lossless_and_dissipative_line_are_closed(eta):
    p=mod.Params(line_transmission=eta)
    r=mod.run(p,steps=15)
    assert r['maximum_single_step_residual_j']<5e-11
    assert r['cumulative']['line_loss_j']>=0
    if eta==1.:
        assert abs(r['cumulative']['line_loss_j'])<1e-14
    else:
        assert r['cumulative']['line_loss_j']>0

@pytest.mark.parametrize('overrides',[
    {'front_m_s':mod.C0*1.00001},{'front_m_s':-1.},{'dt_s':0.},
    {'line_transmission':1.01},{'line_transmission':-.01},{'line_transmission':float('nan')},
    {'l0_h':.003},{'memory_h':0.},{'delay_cells':0},{'characteristic_ohm':-1.},
    {'saturation_h':-.001},{'resistance_ohm':0.},{'phases':1},
])
def test_invalid_physical_parameter_fails_closed(overrides):
    with pytest.raises(ValueError):mod.Params(**overrides).check()

def test_no_measured_v2_geometry_from_model():
    p=mod.Params()
    assert p.cable_m>1000  # coarse time step means *long* illustrative line
    assert p.delay_s>=p.cable_m/mod.C0
    short_delay=.5/(.7*mod.C0)
    assert 2e-9<short_delay<3e-9
    assert p.dt_s/short_delay>1000  # cannot fake a short cable as one solver tick

def test_unforced_motor_can_deliver_negative_terminal_work():
    p=mod.Params(omega_rad_s=0.,line_transmission=1.)
    r=mod.step(p,mod.initial(p,current_a=1.),np.zeros(p.phases))
    assert r['motor_terminal_work_j']<0  # generator direction to line
    assert r['residual_joint_j']==pytest.approx(0,abs=1e-11)

def test_incident_wave_can_supply_positive_terminal_work():
    p=mod.Params(omega_rad_s=0.)
    s=mod.initial(p)
    s['forward'][-1][0]=3.0
    r=mod.step(p,s,np.zeros(p.phases))
    assert r['motor_terminal_work_j']>0
    assert r['residual_joint_j']==pytest.approx(0,abs=1e-11)


def test_only_local_return_wave_drives_feedback():
    p=mod.Params(delay_cells=4,omega_rad_s=0.)
    u=mod.run(p,steps=15,drive_amplitude_v=2.,local_reflection_gain=.35)
    assert abs(u['cumulative']['integrated_balance_error_j'])<1e-10
    with pytest.raises(ValueError):mod.run(p,steps=4,local_reflection_gain=1.)
    with pytest.raises(ValueError):mod.run(p,steps=0)

def test_flux_inverse_and_stored_energy_positive():
    p=mod.Params(phases=7)
    i=np.linspace(.1,2.5,p.phases)
    z=np.linspace(-.3,.1,p.phases)
    lam=mod.flux(p,i,z,theta=.17)
    assert np.max(np.abs(mod.invert_flux(p,lam,z,.17)-i))<1e-10
    assert mod.energy(p,lam,z,.17)>0


def test_no_loss_no_source_no_rotation_total_energy_nonincreasing():
    p=mod.Params(omega_rad_s=0.)
    state=mod.initial(p,current_a=1.,memory=.2)
    def E(s):
        return mod.energy(p,s['flux'],s['memory'],s['theta']) + p.dt_s/p.characteristic_ohm*\
            (np.sum(s['forward']**2)+np.sum(s['backward']**2))
    initial_e=E(state)
    for _ in range(7):
        r=mod.step(p,state,np.zeros(p.phases));state=r['state']
        assert E(state)<=initial_e+1e-11
        assert r['residual_joint_j']==pytest.approx(0,abs=1e-11)
        initial_e=E(state)

@pytest.mark.parametrize('cells',(1,2,3))
def test_correct_05m_cable_causal_time_and_short_step_energy(cells):
    p=mod.Params(dt_s=.5/(.7*mod.C0*cells),delay_cells=cells)
    r=mod.run(p,steps=12)
    assert abs(p.cable_m-.5)<1e-12
    assert r['maximum_single_step_residual_j']<2e-12
    assert abs(r['cumulative']['integrated_balance_error_j'])<2e-12
    assert p.delay_s==pytest.approx(.5/(.7*mod.C0))
