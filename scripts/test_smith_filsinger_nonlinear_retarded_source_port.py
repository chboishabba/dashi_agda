#!/usr/bin/env python3
"""F10-PLASMA/F13-NL/F15 source-first conditional model regression."""
from dataclasses import replace
import pytest
from check_smith_filsinger_nonlinear_retarded_source_port import (
    Parameters, exact_identity_checks, passive_admittance,
    finite_passive_admittance_test, channel_conductance, rates,
    residual_at, simulate, run)


def test_exact_plasma_energy_and_nonlinear_iv_identities():
    assert exact_identity_checks()


def test_passive_multipole_positive_real_and_dispersive():
    assert finite_passive_admittance_test()
    values=[passive_admittance(f,1e-8,1e-9,[(.1,20.)],
             [(.2,.5,45.)]) for f in [0,.3,1,7,30,100]]
    assert all(v.real>=0 for v in values)
    assert max(abs(v.imag) for v in values)>0


def test_negative_dissipation_rejected():
    with pytest.raises(ValueError):
        passive_admittance(1,0,0,[(1.,-1.)])
    with pytest.raises(ValueError):
        passive_admittance(1,0,0,[],[(.1,-1,5)])


def test_plasma_conductance_increases_with_carriers():
    p=Parameters()
    assert channel_conductance(1e20,p)>1000*channel_conductance(1e15,p)
    outer=1/p.exterior_resistance_ohm
    g=channel_conductance(1e20,p)
    series=g*outer/(g+outer)
    assert series<outer  # high local sigma cannot bypass external supply path


def test_current_time_energy_balance():
    p=Parameters()
    for n in (1e12,1e15,1e18,1e20):
        assert abs(residual_at(.1,[200.,n],p))<1e-7


def test_controlled_and_baseline_source_work_not_claimed_as_solar():
    p=Parameters()
    base=simulate(p,duration_s=.05)
    on=simulate(replace(p,ionization_rate_s=5.,controller_W=2.),
                duration_s=.05)
    for r in (base,on):
        assert abs(r['ledger_residual_J'])<1e-5
        assert r['max_instantaneous_residual_J_s']<1e-5
        assert 'not source identity' in r['valid']


def test_no_external_source_and_no_ionization_no_load():
    p=Parameters(source_background_V=0.,source_ac_V=0.,
                 n_initial_m3=0.,spontaneous_pairs_m3_s=0.)
    r=simulate(p,duration_s=.05)
    assert r['source_signed_J']==0.
    assert r['load_J']==0.


def test_ion_creation_paid_for_externally():
    p=Parameters(source_background_V=0.,source_ac_V=0.,
                 ionization_rate_s=4.,controller_W=1.)
    r=simulate(p,duration_s=.05)
    assert r['ionization_creation_pump_J']>0.
    assert r['controller_overhead_J']>0.


def test_model_preserves_original_evidence_gates():
    result=run()
    assert 'source_first P1/P2 R2/R3 still null' in result['hard_gates']
