"""Fail-closed source-bounded efficiency audit for a hypothetical V2 analogue."""
from __future__ import annotations
from dataclasses import replace
import importlib.util
import math
from pathlib import Path
import sys
import pytest

SCRIPT=Path(__file__).resolve().parents[1]/'scripts/v2_source_bounded_efficiency_maxcut.py'
SPEC=importlib.util.spec_from_file_location('v2_efficiency_cut',SCRIPT)
v2=importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name]=v2
SPEC.loader.exec_module(v2)


def test_same_mechanical_resource_all_four():
    m=v2.Machine(); r=v2.comparison(m)
    assert set(r['results'])=={'ordinary_loading','pulse_timing_only','recovery_only','combined_pulsing_and_recovery'}
    for row in r['results'].values():
        assert abs(row['mechanical_input_w']-45)<1e-8
        assert row['same_shaft_w']
        assert row['storage_delta_j_per_rev']==0
        assert row['admissible_at_assumed_peak_current']
        assert abs(row['accounting_residual_w'])<1e-8
        assert row['useful_bus_w']<=row['mechanical_input_w']+1e-9


def test_conventional_is_not_a_zero_recovery_strawman():
    m=v2.Machine()
    conventional=v2.arm(m,0,timed=False,recovery=False)
    assert conventional['recovered_clamp_w']>0
    assert conventional['off_clamp_dump_w']>0
    assert conventional['recovered_clamp_w']+conventional['off_clamp_dump_w']==pytest.approx(conventional['off_clamp_available_w'])


def test_four_arm_ranking_for_stated_illustration():
    rows=v2.comparison(v2.Machine())['results']
    assert 10<rows['ordinary_loading']['useful_bus_w']<12
    assert 11<rows['pulse_timing_only']['useful_bus_w']<13
    assert 20<rows['recovery_only']['useful_bus_w']<23
    assert 22<rows['combined_pulsing_and_recovery']['useful_bus_w']<25
    assert rows['pulse_timing_only']['q']>0
    assert rows['combined_pulsing_and_recovery']['q']>rows['pulse_timing_only']['q']


def test_torque_fixed_and_current_increases_with_narrower_pulses():
    m=v2.Machine()
    qs=(0.,.15,.5,.7)
    currents=[v2.current_at_fixed_shaft(m,q) for q in qs]
    assert all(x<y for x,y in zip(currents,currents[1:]))
    for q in qs:
        assert v2.arm(m,q,timed=True,recovery=True)['mechanical_input_w']==pytest.approx(m.shaft_power_w,rel=1e-12)


def test_peak_current_cap_rejects_unattainable_or_bad_q():
    m=v2.Machine(); lim=v2.q_limit(m)
    assert 0<lim<1
    assert v2.current_at_fixed_shaft(m,lim)==pytest.approx(m.peak_current_limit_a,rel=1e-10)
    for q in (-.1,lim+1e-3,1.):
        with pytest.raises(ValueError):v2.current_at_fixed_shaft(m,q)
    with pytest.raises(ValueError):v2.q_limit(replace(m,peak_current_limit_a=1.))


@pytest.mark.parametrize('q', [0.,.05,.2,.4,.7,.85])
def test_independent_signed_terminal_energy_conservation(q):
    m=v2.Machine(); r=v2.arm(m,q,timed=q>0,recovery=True)
    assert r['terminal_gross_recovery_available_w']-r['terminal_gross_drive_w']==pytest.approx(
        r['mechanical_input_w']-r['losses_w']['copper_w'],abs=1e-9)
    assert r['mechanical_input_w']==pytest.approx(r['useful_bus_w']+sum(r['losses_w'].values()),abs=1e-8)
    assert r['recovered_clamp_w']<=r['off_clamp_available_w']+1e-9


@pytest.mark.parametrize('phase',[-math.pi,-1.,0.,.8,math.pi])
@pytest.mark.parametrize('current',[0.,.1,2.,5.,8.,17.])
def test_convex_saturating_coenergy_and_nonnegative_storage(phase,current):
    m=v2.Machine()
    derivative=m.mean_inductance_h+m.varying_inductance_h*math.cos(phase)/(math.cosh(current/m.sat_current_a)**2)
    assert derivative>=m.mean_inductance_h-m.varying_inductance_h
    assert v2.stored(m,phase,current)>=-1e-12
    delta=1e-5
    numerical=(v2.coenergy(m,phase,current+delta)-v2.coenergy(m,phase,current-delta))/(2*delta)
    assert numerical==pytest.approx(v2.flux(m,phase,current),abs=1e-9)


def test_symbolic_general_coenergy_identity():
    import sympy as sp
    theta,i,w,di=sp.symbols('theta i omega di',real=True)
    W=sp.Function('Wprime')(theta,i)
    lam=sp.diff(W,i)
    U=i*lam-W
    assert sp.simplify(i*(sp.diff(lam,i)*di+sp.diff(lam,theta)*w)
        -(sp.diff(U,i)*di+sp.diff(U,theta)*w)-sp.diff(W,theta)*w)==0


def test_switch_field_energy_is_accounted_not_a_new_source():
    m=v2.Machine(); row=v2.arm(m,.45,timed=True,recovery=True)
    assert row['off_clamp_available_w']>0
    assert row['terminal_gross_recovery_available_w']>row['mechanical_input_w']
    assert row['terminal_gross_drive_w']>row['mechanical_input_w']
    assert row['useful_bus_w']<row['mechanical_input_w']


def test_recovery_analytic_increment_and_controller_cost():
    m=v2.Machine(); a=v2.arm(m,0,timed=False,recovery=False);b=v2.arm(m,0,timed=False,recovery=True)
    old_switch=a['losses_w']['switching_w']
    expected=(m.eta_clamp_recovered-m.eta_clamp_basic)*a['off_clamp_available_w'] \
              +(1-m.soft_switch_fraction)*old_switch-m.recovery_controller_w
    assert b['useful_bus_w']-a['useful_bus_w']==pytest.approx(expected,abs=1e-9)


def test_negative_control_expensive_recovery_can_hurt():
    m=replace(v2.Machine(),recovery_controller_w=30.)
    a=v2.arm(m,0,timed=False,recovery=False)
    b=v2.arm(m,0,timed=False,recovery=True)
    assert b['useful_bus_w']<a['useful_bus_w']
    assert v2.comparison(m)['results']['combined_pulsing_and_recovery']['useful_bus_w']<a['useful_bus_w']


def test_identical_converter_has_no_free_recovery_gain():
    m=v2.Machine()
    m=replace(m,eta_clamp_recovered=m.eta_clamp_basic,
              soft_switch_fraction=1.,recovery_controller_w=0.)
    a=v2.arm(m,0,timed=False,recovery=False)
    b=v2.arm(m,0,timed=False,recovery=True)
    assert b['useful_bus_w']==pytest.approx(a['useful_bus_w'],abs=1e-10)


def test_perfect_converter_cannot_exceed_mechanical_input():
    m=replace(v2.Machine(),eta_fwd=1.,eta_running_regen=1.,eta_clamp_basic=1.,
              eta_clamp_recovered=1.,switch_fixed_j=0.,switch_per_i2_j=0.,
              pulse_logic_w=0.,recovery_controller_w=0.,core_loss_w=0.)
    for q in (0.,.25,.5):
        r=v2.arm(m,q,timed=True,recovery=True)
        assert r['total_losses_w']==pytest.approx(r['losses_w']['copper_w'])
        assert r['useful_bus_w']==pytest.approx(m.shaft_power_w-r['losses_w']['copper_w'],abs=1e-9)


def test_loaded_unloaded_boundary_stated_45w_requirement():
    r=v2.load_intervention_requirement()
    assert r['required_loss_delta_w']==-45
    assert r['motor_display_delta_w']==0
    assert v2.load_intervention_requirement(displayed_input_loaded_w=287,displayed_input_unloaded_w=285)['required_loss_delta_w']==-43
    assert v2.load_intervention_requirement(displayed_input_loaded_w=285,displayed_input_unloaded_w=287)['required_loss_delta_w']==-47


def test_auxiliary_storage_or_displaced_load_disambiguation():
    assert v2.load_intervention_requirement(delta_auxiliary_w=45)['required_loss_delta_w']==0
    assert v2.load_intervention_requirement(delta_unaccounted_input_w=45)['required_loss_delta_w']==0
    assert v2.load_intervention_requirement(delta_storage_rate_w=-45)['required_loss_delta_w']==0
    assert v2.load_intervention_requirement(delta_other_load_w=-45)['required_loss_delta_w']==0


def test_real_source_is_not_implicitly_identified_or_sufficiently_explained():
    c=v2.comparison(v2.Machine())
    assert c['difference_from_ordinary_w']['combined_pulsing_and_recovery']<45.
    assert c['four_way_not_same_as_loaded_unloaded'].startswith('yes')
    assert c['machine']['shaft_power_w']==45.
    assert c['source_reported_rpm_only']==2354.


def test_sensitivity_has_good_and_bad_recovery():
    r=v2.sweep(); assert len(r['rows'])>30
    assert 0<r['negative_recovery_examples']<len(r['rows'])
    assert 0<r['negative_combined_examples']<len(r['rows'])


def test_parameter_validation():
    bad=[dict(mean_inductance_h=.005),dict(eta_fwd=0.),dict(eta_clamp_basic=1.1),
         dict(soft_switch_fraction=0.),dict(recovery_controller_w=-1.),
         dict(pole_harmonic=0),dict(resistance_ohm=-1),dict(sat_current_a=-1.)]
    for change in bad:
        with pytest.raises(ValueError):v2.Machine(**{**v2.asdict(v2.Machine()),**change}).validate()


def test_linear_saturation_limit_agrees_with_existing_donor():
    # This module exists in canonical DASHI. Reuse it rather than claiming
    # the linear benchmark is a new derivation of the Don Smith donor.
    donor=SCRIPT.parent/'check_v2_pulse_nonlinear_recovery.py'
    spec=importlib.util.spec_from_file_location('v2_original_linear_donor',donor)
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    m=replace(v2.Machine(),sat_current_a=10000.)
    for q in (0.,.5,.7):
        newer=v2.arm(m,q,timed=True,recovery=True)
        original=module.pulse_window(module.Candidate(),q)
        assert newer['peak_current_a']==pytest.approx(original['peak_current_a'],rel=3e-7)
        assert newer['losses_w']['copper_w']==pytest.approx(original['copper_loss_w'],rel=3e-7)
        assert newer['mechanical_input_w']==pytest.approx(original['mechanical_extraction_w'],rel=3e-7)


def test_recovery_pulse_interaction_is_reported_not_assumed_positive():
    r=v2.comparison(v2.Machine())
    a,b,c,d=[r['results'][k]['useful_bus_w'] for k in (
        'ordinary_loading','pulse_timing_only','recovery_only','combined_pulsing_and_recovery')]
    assert r['timing_recovery_interaction_w']==pytest.approx(d-b-c+a,abs=1e-10)


def test_no_artificial_energy_source_from_zero_shaft_change():
    m=v2.Machine()
    r=v2.comparison(m)
    for name,x in r['results'].items():
        assert x['terminal_gross_recovery_available_w']>0
        assert x['storage_delta_j_per_rev']==0
        assert x['storage_scope'].startswith('Only this ideal winding')
        assert sum(x['losses_w'].values())>=0


def test_four_different_reel_equivalent_worlds_are_energy_closed():
    w=v2.reel_counterworlds()
    assert w['identical_reel_displays_not_identifying_mechanism']
    assert len(w['worlds'])==4
    assert all(v['closed_residual_w']==0 for v in w['worlds'].values())
    assert len({v['true_input_w'] for v in w['worlds'].values()})>1
    assert len({v['storage_rate_w'] for v in w['worlds'].values()})>1
    assert len({v['aux_w'] for v in w['worlds'].values()})>1

def test_timing_overhead_can_erase_a_small_pulse_gain():
    m=replace(v2.Machine(),pulse_logic_w=6.)
    c=v2.comparison(m)
    assert c['results']['pulse_timing_only']['useful_bus_w']<c['results']['ordinary_loading']['useful_bus_w']
