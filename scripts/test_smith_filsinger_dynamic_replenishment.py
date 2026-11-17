#!/usr/bin/env python3
"""Conditional continuous time source / exact segment integral tests."""
from dataclasses import replace
import math
import pytest
import numpy as np
from check_smith_filsinger_dynamic_replenishment import (
    Source,Branches,exact_segment,one_cycle,periodic_state,
    fairweather_column,compare)

@pytest.mark.parametrize('g,G,C,V,v0,dt',[
    (1,1,1,1,.5,1),(0,1,1,1,1,10),(1,0,1,1,.5,4),
    (.1,1,100,2,0,20),(.001,.03,5,2,1,50),
    (0,0,1,2,1,7),(1,1,1,1,2,1),(.3,2,1,1,-.2,.1),
    (1,1,1,1,.5,0)])
def test_exact_segment_balance(g,G,C,V,v0,dt):
    r=exact_segment(Source(V,g,C,0),v0,G,dt)
    assert abs(r.residual)<2e-11
    assert r.match_deficit >= -2e-11
    assert abs(r.terminal+r.match_deficit-g*V*V*dt/4)<2e-11
    assert abs(r.terminal-r.load-r.delta_store)<2e-11

@pytest.mark.parametrize('phase',[0,math.pi/4,math.pi/2,3*math.pi/4,math.pi])
def test_periodic_cycle_same_storage_phase(phase):
    s=Source()
    b=Branches(phase=phase)
    v=periodic_state(s,b)
    r=one_cycle(s,b,v)
    assert abs(r['v_final']-v)<3e-13
    assert abs(r['delta_store'])<3e-13
    assert abs(r['whole_cycle_residual'])<3e-12
    assert abs(r['terminal_cap_residual'])<3e-12
    assert r['load']<=r['source_cap']+3e-12
    assert abs(r['load']-r['terminal'])<3e-12

@pytest.mark.parametrize('phase',[0,.2,math.pi/2,math.pi,5.5])
def test_overcharged_transient_is_not_replenishment(phase):
    b=Branches(phase=phase)
    r=one_cycle(Source(),b,v0=2.)
    assert r['delta_store']<0
    assert r['load']+r['delta_store']<=r['source_cap']+1e-10
    assert abs(r['upstream']-r['load']-r['feeder_heat']-r['delta_store'])<1e-10

@pytest.mark.parametrize('phase',[0,.7,math.pi,5.5])
def test_no_natural_input_means_donor_depletion(phase):
    s=Source(upstream_v=10,feed_g=0,capacitance=1,controller_cost_rate=.03)
    r=one_cycle(s,Branches(phase=phase,period=20),1.)
    assert r['upstream']==0 and r['terminal']==0
    assert r['load']>0 and r['delta_store']<0
    assert abs(r['load']+r['delta_store'])<1e-11
    assert r['load']<.5+1e-12

@pytest.mark.parametrize('phase',[0.,math.pi/3,math.pi])
def test_true_source_free_cannot_deliver(phase):
    s=Source(upstream_v=0.,feed_g=0.,capacitance=1.)
    r=one_cycle(s,Branches(phase=phase),v0=0)
    assert r['load']==0 and r['upstream']==0 and r['delta_store']==0

@pytest.mark.parametrize('phase',[0.,math.pi/2,math.pi])
def test_controller_cost_cannot_be_mislabelled_as_natural(phase):
    a=one_cycle(Source(controller_cost_rate=0),Branches(phase=phase),v0=.5)
    b=one_cycle(Source(controller_cost_rate=.2),Branches(phase=phase),v0=.5)
    assert b['upstream']==pytest.approx(a['upstream'])
    assert b['load']==pytest.approx(a['load'])
    assert b['controller']==pytest.approx(.2*2*math.pi)
    assert b['net_load_after_controller']==pytest.approx(a['load']-.2*2*math.pi)

def test_fixed_source_matching_equality():
    s=Source(upstream_v=1,feed_g=1,capacitance=1,controller_cost_rate=0)
    b=Branches(phase=math.pi)
    r=one_cycle(s,b,periodic_state(s,b))
    assert r['match_deficit']<1e-12
    assert r['load']==pytest.approx(2*math.pi/4,abs=1e-12)

def test_anti_phase_can_win_for_fixed_source():
    rows=compare()
    assert rows[-1]['load']>rows[0]['load']
    assert rows[-1]['match_deficit']<=rows[0]['match_deficit']+1e-10

def test_dynamic_source_matching_fine_resolution_convergence():
    s=Source()
    a=Branches(phase=.6,intervals=256)
    b=replace(a,intervals=512)
    c=replace(a,intervals=1024)
    ra=one_cycle(s,a,periodic_state(s,a))
    rb=one_cycle(s,b,periodic_state(s,b))
    rc=one_cycle(s,c,periodic_state(s,c))
    assert abs(rb['load']-rc['load'])<abs(ra['load']-rb['load'])
    assert abs(rb['load']-rc['load'])<2e-5

def test_fairweather_fixed_source_ideal_not_aperture():
    r=fairweather_column()
    assert r['short_circuit_current_A']==pytest.approx(2.36e-12)
    assert r['matched_power_W']==pytest.approx(1.475e-7)
    assert r['matched_energy_60s_J']==pytest.approx(8.85e-6)
    assert 'NOT Filsinger' in r['source_identity']

def test_one_m2_ideal_source_not_point_electrode():
    r=fairweather_column(3.)
    assert r['matched_power_W']==pytest.approx(3*1.475e-7)

def test_nonnegative_source_input_failures():
    with pytest.raises(ValueError):one_cycle(Source(feed_g=-1))
    with pytest.raises(ValueError):one_cycle(Source(capacitance=0))
    with pytest.raises(ValueError):one_cycle(Source(),Branches(amp_g=.7))
    with pytest.raises(ValueError):one_cycle(Source(),Branches(period=-1))

def test_linear_source_input_return_sign_when_overcharged():
    p=Source(upstream_v=1,feed_g=1,capacitance=2)
    r=exact_segment(p,4,0,.05)
    assert r.upstream<0  # initial capacitor returns current to upstream supply
    assert r.terminal<0
    assert r.feeder_heat>0

def test_matching_bound_survives_fast_switched_conductances():
    s=Source(upstream_v=1,feed_g=.3,capacitance=.15)
    for ph in (0,.3,2.1,math.pi):
        b=Branches(mean_g=.4,amp_g=.39,phase=ph,intervals=64)
        r=one_cycle(s,b,v0=.6)
        assert r['terminal']<=r['source_cap']+1e-9
        assert r['load']+r['delta_store']<=r['source_cap']+1e-9
