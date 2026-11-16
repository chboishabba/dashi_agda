"""Maximum-cut experiment controls and smooth-cycle restricted model acceptance."""
import sys, math
from pathlib import Path
from dataclasses import replace
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import v2_omega_smooth_storage_metrology_maxcut as z

@pytest.fixture(scope='module')
def full():return z.run()

def test_model_is_not_original(full):
    assert full['original_v2_physical_identified'] is False
    assert full['agda_kernel_accepted'] is False

def test_one_shared_shaft_for_every_enumerated_candidate(full):
    assert len(full['frontier']['candidates'])==30
    assert all(abs(c['shaft_w']-45)<1e-7 for c in full['frontier']['candidates'])

def test_winding_cycle_and_mean_energy_account(full):
    for c in full['frontier']['candidates']:
        assert c['windings_periodic_by_analytic_waveform']
        assert abs(c['total_signed_energy_residual_w'])<1e-7
        assert abs(c['magnetic_signed_energy_residual_w'])<1e-7
        assert abs(c['bus_energy_endpoint_residual_j'])<1e-9
        assert c['net_bus_w']<=c['shaft_w']
        assert c['copper_w']>=0 and c['converter_loss_w']>=0

def test_finite_slew_and_voltage_certificate_is_not_sample_only(full):
    for c in full['frontier']['candidates']:
        assert c['continuous_voltage_grid_lipschitz_upper_v']>=c['peak_terminal_voltage_v']
        assert c['analytic_current_upper_a']>=c['peak_current_a']-1e-7
        assert c['analytic_slew_upper_a_s']>=c['peak_current_slew_a_s']-1e-7
        assert not c['continuous_bus_and_thermal_certified']
    rows=[c for c in full['frontier']['candidates'] if c['continuous_winding_envelope_certified']]
    assert len(rows)==full['frontier']['continuous_winding_envelope_count']>0
    assert all(c['continuous_voltage_grid_lipschitz_upper_v']<=320 for c in rows)
    assert all(c['continuous_dc_bus_enclosure_certified'] for c in rows)

def test_bus_voltage_can_supply_winding_voltage(full):
    for c in full['frontier']['candidates']:
        if c['continuous_winding_envelope_certified']:
            p=full['plant']
            assert c['continuous_voltage_grid_lipschitz_upper_v']<p['bus_min_v']
            assert c['continuous_dc_bus_energy_lower_j']>0

def test_recovery_advantage_is_certified_conditional_on_same_waveform(full):
    g=full['frontier']
    low,high=g['enhanced_same_waveform_gain_interval_w']
    assert 0<low<g['enhanced_same_waveform_gain_w']<high
    assert g['enhanced_same_waveform_gain_certified_positive']
    assert 6<low<8
    assert g['best_with_conservative_winding_envelope']['q']==0
    assert g['best_with_conservative_winding_envelope']['mode']=='enhanced_recovery'

def test_winding_must_not_be_confused_with_whole_device(full):
    for c in full['frontier']['candidates']:
        assert 'approximation' in c['sampled_approximation'] or 'samples' in c['sampled_approximation']
        assert c['continuous_bus_and_thermal_certified'] is False

@pytest.mark.parametrize('q,lead',[(0,0),(.15,0),(.30,.15),(.60,-.15)])
def test_arbitrary_smooth_inputs_have_closed_mean_port(q,lead):
    c=z.profile(z.Plant(n=2048),q,lead,require_feasible=False)
    assert abs(c['shaft_w']-45)<1e-7
    assert abs(c['total_signed_energy_residual_w'])<1e-7
    assert c['peak_current_a']>=0

@pytest.mark.parametrize('kwargs',[
    {'eta_forward':0}, {'eta_reverse':1.2}, {'L0_h':.002},
    {'bus_min_v':340}, {'capacitor_f':-1}, {'R_ohm':0}, {'Vlim_v':-1}])
def test_invalid_component_or_converter(kwargs):
    with pytest.raises(ValueError):z.profile(replace(z.Plant(),**kwargs),0.,0.)

def test_high_controller_overhead_can_reverse_same_wave_recovery():
    p=z.Plant(n=1024)
    baseline=z.profile(p,0,0,eta_reverse=.95,require_feasible=False)
    recovery=z.profile(p,0,0,eta_reverse=.99,control_extra_w=20,require_feasible=False)
    assert recovery['net_bus_w']<baseline['net_bus_w']

def test_strict_voltage_guard():
    p=replace(z.Plant(n=1024),Vlim_v=150)
    c=z.profile(p,0.,0.,require_feasible=False)
    assert not c['continuous_winding_envelope_certified']
    with pytest.raises(ValueError):z.profile(p,0.,0.,require_feasible=True)

@pytest.mark.parametrize('duration',[.1,1.,10.,30.])
def test_inertial_storage_conservation_bound(duration):
    x=z.flywheel_deficit(duration_s=duration)
    assert math.isclose(x['minimum_inertia_kgm2'],z.flywheel_deficit()['minimum_inertia_kgm2']*duration)
    assert x['final_rpm_if_only_storage']<=2354

def test_inertial_source_requires_speed_drop_or_inertia():
    a=z.flywheel_deficit(duration_s=10,inertia_kgm2=.01)
    assert a['rotor_exhausted_before_duration']
    b=z.flywheel_deficit(duration_s=1,tolerance_fraction=.01,inertia_kgm2=a['minimum_inertia_kgm2']*2)
    assert b['final_rpm_if_only_storage']>0

def test_observation_matrix_proves_meter_nonidentifiability(full):
    x=full['meter_rank']
    assert x['meter_equations_rank']==1 and x['nullity']==3
    assert x['minimal_extra_independent_constraints']==3

def test_meter_only_loss_suppression_bounds():
    x=z.loss_interval()
    assert x['required_loss_suppression_interval_w']==[43.,47.]

def test_unmeasured_aux_and_storage_destroy_loss_deduction():
    a=z.loss_interval(delta_aux_interval_w=(-50,50),delta_storage_rate_interval_w=(-50,50))
    lo,hi=a['required_loss_suppression_interval_w']
    assert lo<0<hi

def test_measured_other_port_changes_loss_requirement():
    x=z.loss_interval(delta_other_output_interval_w=(5,5),delta_input_interval_w=(0,0))
    assert x['required_loss_suppression_interval_w']==[50.,50.]

@pytest.mark.parametrize('bad', [(-1,1),(3,-3)])
def test_reject_impossible_intervals(bad):
    if bad==(-1,1):
        with pytest.raises(ValueError):z.loss_interval(load_added_w=-1.)
    else:
        with pytest.raises(ValueError):z.loss_interval(delta_aux_interval_w=bad)
