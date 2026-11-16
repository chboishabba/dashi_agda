#!/usr/bin/env python3
"""Source-equivalent acceptance for conditional midpoint/coherent source work."""
import math
from dataclasses import replace
import numpy as np
import pytest
from check_smith_filsinger_midpoint_phase_work import (Params,solve,matrices,
  coherent_phase_scan,incoherent_phase_average,phase_load_search,wrap_phase)

def test_two_port_signed_energy_identity():
    for phase in np.linspace(0,2*math.pi,13):
        for source in (0.,.35,.7):
            r=solve(replace(Params(),natural_amp=source,controller_phase=float(phase)))
            assert abs(r['balance_residual'])<1e-12

def test_matched_empty_environment_cannot_be_harvested():
    for phase in (0.,math.pi/3,math.pi/2,math.pi):
        assert solve(replace(Params(),controller_phase=phase,natural_amp=0))['natural_net']<=1e-12

def test_controller_off_energy_is_natural_only():
    r=solve(replace(Params(),controller_amp=0.))
    assert r['controller_net']<=1e-12
    assert r['load']+r['heat']<=r['natural_in']+1e-12

def test_empty_state_source_free():
    r=solve(replace(Params(),natural_amp=0,controller_amp=0))
    assert r['load']==pytest.approx(0.)
    assert r['natural_net']==pytest.approx(0.)

def test_common_drive_relative_phase_stable_with_amplitude():
    a=solve(replace(Params(),natural_amp=0.,controller_amp=.1))
    b=solve(replace(Params(),natural_amp=0.,controller_amp=.9))
    assert abs(wrap_phase(a['relative_phase_rad']-b['relative_phase_rad']))<1e-12

def test_free_running_split_has_no_common_lock():
    p=replace(Params(),conservative_coupling=0.,detuning=.08)
    k,omega,g,m=matrices(p)
    assert abs((omega[0,0]-omega[1,1])-.16)<1e-15
    assert abs(wrap_phase(.16*10))>.1

def test_phase_at_interaction_differs_after_retarded_path():
    p=Params()
    start=solve(p)
    delay=solve(replace(p,branch_delays=(0.,.2)))
    assert abs(wrap_phase(delay['relative_phase_rad']-start['relative_phase_rad']+.2))<1e-12

def test_load_perturbs_relative_phase():
    p=Params()
    low=solve(replace(p,gamma_load=.01,natural_amp=0.))
    high=solve(replace(p,gamma_load=.16,natural_amp=0.))
    assert abs(wrap_phase(low['relative_phase_rad']-high['relative_phase_rad']))>1e-3

def test_random_natural_phase_erases_controller_phase_advantage():
    rows=incoherent_phase_average(Params(),128)
    for key in ('natural_net','controller_net','load','heat'):
        assert max(x[key] for x in rows)-min(x[key] for x in rows)<2e-12

def test_phase_sensitive_coherent_exchange():
    rows=coherent_phase_scan(Params(),72)
    assert len(rows)==72
    assert max(x['natural_net'] for x in rows)-min(x['natural_net'] for x in rows)>.005
    assert all(abs(x['balance_residual'])<1e-12 for x in rows)

def test_natural_incident_not_equal_natural_harvest():
    r=solve(Params())
    assert r['natural_net']<=r['natural_in']+1e-12
    assert r['natural_out']>=0

def test_fixed_geometry_not_fixed_quadrature():
    p=Params()
    a=solve(replace(p,natural_amp=0.,detuning=0.))
    b=solve(replace(p,natural_amp=0.,detuning=.12))
    assert abs(wrap_phase(a['relative_phase_rad']-b['relative_phase_rad']))>.05

def test_scan_distinguishes_phase_optima():
    r=phase_load_search(Params())
    assert r['cases']==1728
    assert r['max_load']['load_power']>=r['max_circularity']['load_power']-1e-13
    assert r['max_load_given_positive_env']['natural_net']>0
    assert r['max_positive_env_net']['natural_net']>=r['max_load_given_positive_env']['natural_net']-1e-13

def test_passivity_source_total():
    for n in range(32):
        p=replace(Params(),controller_phase=.19*n,natural_phase=.51*n,
                  gamma_load=.005+n*.004)
        r=solve(p)
        assert r['load']+r['heat']<=r['natural_in']+r['controller_in']+1e-12

def test_negative_rates_rejected():
    with pytest.raises(ValueError):solve(replace(Params(),gamma_load=-.01))
    with pytest.raises(ValueError):solve(replace(Params(),branch_delays=(-.1,0)))

def test_prior_reflection_producer_energy_closure():
    from smith_filsinger_reflection_energy_cut import reflection_and_extraction
    assert sum(reflection_and_extraction(.04,.02,.06).values())==pytest.approx(1.)

def test_prior_ratio_producer_single_source_budget():
    from smith_filsinger_single_wave_fibonacci_modes import response
    assert response(1.5)['useful']<=1+1e-12
