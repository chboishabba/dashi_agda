#!/usr/bin/env python3
"""Exact-source conditional test suite, not original Filsinger measurements."""
from dataclasses import replace
import math
import numpy as np
import pytest
from check_smith_filsinger_midpoint_dc_source_matching import (
    DCParams,cycle,run,exact_thevenin_square)

def test_exact_matching_square():assert exact_thevenin_square()
def test_anti_phase_flat_total_conductance():assert cycle(math.pi)['ripple_G']<1e-12
def test_anti_phase_reaches_fixed_thevenin_ceiling():
    p=DCParams()
    assert cycle(math.pi,p)['load_work']==pytest.approx(p.voc**2/(4*p.rs))
def test_inphase_is_below_antiphase():
    assert cycle(0)['load_work']<cycle(math.pi)['load_work']
def test_phase_grid_best_is_opposition():
    assert run()['best_in_fixed_rs_one']['phase_rad']==pytest.approx(math.pi)
def test_exact_instantaneous_budget():
    for ph in np.linspace(0,2*math.pi,13):
        assert cycle(float(ph))['energy_residual']<1e-12
def test_no_natural_dc_voltage_no_natural_work():
    r=cycle(.17,replace(DCParams(),voc=0))
    assert r['natural_supplied']==pytest.approx(0)
    assert r['load_work']==pytest.approx(0)
def test_controller_cost_subtracted_not_harvested():
    a=cycle(math.pi,replace(DCParams(),controller_cost=0))
    b=cycle(math.pi,replace(DCParams(),controller_cost=.02))
    assert b['net_useful_after_controller_cost']==pytest.approx(a['load_work']-.02)
    assert b['natural_supplied']==pytest.approx(a['natural_supplied'])
def test_source_resistance_mismatch_changes_optimum():
    assert run()['source_resistance_mismatch_best']['phase_rad']!=pytest.approx(math.pi)
def test_no_negative_conductance():
    with pytest.raises(ValueError):
        cycle(0,replace(DCParams(),amplitude_branch_G=.7))
def test_zero_controller_negative_forbidden():
    with pytest.raises(ValueError):
        cycle(0,replace(DCParams(),controller_cost=-1))
def test_passive_load_cannot_exceed_matched_source():
    for x in np.linspace(0,2*math.pi,71):
        assert cycle(float(x))['load_work']<=.25+1e-12
