"""Same-shaft, finite-averaged-bus control negative test against prior owner."""
from __future__ import annotations
from pathlib import Path
import importlib.util,sys
import pytest

P=Path(__file__).resolve().parents[1]/'scripts/v2_fixed_shaft_pwm_negative_control.py'
S=importlib.util.spec_from_file_location('pwm_v2_steelman_negative',P)
M=importlib.util.module_from_spec(S);sys.modules[S.name]=M;S.loader.exec_module(M)

@pytest.fixture(scope='module')
def rows():return M.run()

def test_all_five_match_shaft_and_accepted_bounds(rows):
    assert len(rows['arms'])==5
    for r in rows['arms'].values():
        assert abs(r['power_mechanical_extract_w']-45)<.03
        assert r['feasible'] and r['magnetically_periodic_2pct']
        assert r['max_voltage_v']<=320+1e-8
        assert r['power_storage_change_w']<.02

def test_timing_can_hurt_even_when_copper_falls(rows):
    a=rows['arms']['ordinary_loading'];b=rows['arms']['pulse_timing_only']
    assert b['power_copper_w']<a['power_copper_w']
    assert b['power_bus_w']<a['power_bus_w']

def test_recovery_still_has_signed_finite_cost(rows):
    a=rows['arms']['ordinary_loading'];c=rows['arms']['recovery_only']
    assert c['gross_regen_w']>0 and c['gross_drive_w']>0
    assert c['power_bus_w']>a['power_bus_w']
    assert c['power_bus_w']<c['power_mechanical_extract_w']

def test_combined_not_necessarily_beats_recovery_only(rows):
    c=rows['arms']['recovery_only'];d=rows['arms']['combined_pulsing_and_recovery']
    assert d['power_bus_w']<c['power_bus_w']

def test_sharp_pulse_is_worse_due_converter_processing(rows):
    a=rows['arms']['recovery_only'];bad=rows['arms']['over_narrow_pulse_adversary']
    assert bad['power_bus_w']<a['power_bus_w']
    assert bad['gross_regen_w']>a['gross_regen_w']
    assert bad['max_voltage_v']>a['max_voltage_v']

def test_signed_energy_and_thermal_residuals(rows):
    for a in rows['arms'].values():
        assert abs(a['energy_residual_j'])<1e-2
        assert abs(a['bus_energy_residual_j'])<1e-2
        assert abs(a['thermal_energy_residual_j'])<1e-2
