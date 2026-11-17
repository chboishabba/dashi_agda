import math
import pytest
from check_smith_filsinger_local_maxwell_port import symbolic_energy,retardation_diagnostic

def test_exact_local_maxwell_energy_identity():
    assert symbolic_energy()['energy_residual']=='0'
def test_exact_nonlinear_polarization_work_identity():
    assert symbolic_energy()['polarization_residual']=='0'
def test_hall_heating_zero_in_neutral_frame():
    assert symbolic_energy()['hall_neutral_frame_residual']=='0'
def test_hall_neutral_wind_work_can_be_nonzero():
    assert abs(symbolic_energy()['natural_wind_power_example'])>0

def test_two_m_7800Hz_quasistatic_screen():
    r=retardation_diagnostic(2,7800)
    assert r['quasistatic_screen']

def test_full_column_7800hz_not_quasistatic():
    r=retardation_diagnostic(80000,7800)
    assert not r['quasistatic_screen']
    assert r['phase_distance_rad']==pytest.approx(13.078,rel=1e-3)

def test_cannot_use_negative_electrical_clock():
    with pytest.raises(ValueError):retardation_diagnostic(2,-1)

def test_cannot_use_unphysical_front_speed():
    with pytest.raises(ValueError):retardation_diagnostic(2,7800,400000000)
