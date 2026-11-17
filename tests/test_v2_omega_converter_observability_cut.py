import math, pathlib,sys
import pytest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'scripts'))
from v2_omega_converter_observability_cut import *

@pytest.fixture(scope='module')
def base():return converter_admission()

def test_robust_voltage_headroom_tiny(base):assert 0 < base['nominal_voltage_headroom_v'] < .4

def test_resistance_temperature_negative_control():
    b=converter_admission(resistance_error_ohm=.1)
    assert not b['voltage_envelope_certified'] and b['robust_voltage_headroom_v']<0

def test_unmodelled_one_volt_invalidates():assert not converter_admission(voltage_error_v=1.)['voltage_envelope_certified']

def test_nominal_positive_gain(base):assert 7<base['recovery_net_gain_w']<8 and base['gain_certified_positive']

def test_throughput_mechanism(base):
    assert abs(base['recovery_net_gain_w']-(.99-.95)*base['reverse_gross_w']+.4)<1e-9

def test_break_even_eta(base):assert .95 < base['minimum_enhanced_eta_to_break_even'] < .96

def test_control_cost_above_gain_reverses():assert converter_admission(controller_extra_w=9.)['recovery_net_gain_w']<0

def test_stated_no_hardware_cert(base):assert not base['converter_hardware_admitted']

def test_missing_data_explicit(base):assert len(base['required_missing_evidence'])>=4

def test_extreme_eta_input_rejected():
    with pytest.raises(ValueError):converter_admission(enhanced_eta=1.01)

def test_negative_voltage_bound_rejected():
    with pytest.raises(ValueError):converter_admission(voltage_error_v=-1)

def test_complete_identifiability():
    a=experiment_design();assert a['rank']==4 and a['nullity']==0

def test_meter_only_rank_one():
    a=experiment_design(());assert a['rank']==1 and a['nullity']==3

def test_duplicate_meter_does_not_help():
    a=experiment_design(('duplicate_input_output_meter',));assert a['rank']==1

def test_three_causal_independent_ports():
    a=experiment_design(('auxiliary_port','matched_storage_endpoints','other_output_ports'))
    assert a['all_four_unknowns_identifiable'] and a['loss_uniquely_identifiable']

def test_loss_directly_identifiable_even_without_all_ports():
    a=experiment_design(('direct_calorimetry',))
    assert a['loss_uniquely_identifiable'] and not a['all_four_unknowns_identifiable']

def test_correlated_sensor_combination_rank():
    a=experiment_design(('auxiliary_port','combined_storage_other'))
    assert a['rank']==3 and a['loss_uniquely_identifiable'] and not a['all_four_unknowns_identifiable']

def test_three_sensor_rank_independent():
    a=experiment_design(('auxiliary_port','matched_storage_endpoints','other_output_ports'))
    assert a['rank']==4

def test_unknown_sensor_rejected():
    with pytest.raises(ValueError):experiment_design(('random',))

def test_duplicate_sensor_rejected():
    with pytest.raises(ValueError):experiment_design(('auxiliary_port','auxiliary_port'))

def test_loss_suppression_interval():
    a=loss_suppression_interval();assert a['guaranteed_suppression_interval_w']==[38,52]

def test_unspecified_ports_do_not_certify():
    a=loss_suppression_interval(auxiliary_error_w=100,storage_error_w=100)
    assert not a['suppression_sign_certified']

def test_symmetric_error_budget():
    a=loss_suppression_interval(load_error_w=2,input_error_w=2,auxiliary_error_w=2,storage_error_w=2,other_error_w=2)
    assert a['guaranteed_suppression_interval_w']==[35,55]

def test_loss_sign_and_storage():
    a=loss_suppression_interval(storage_delta_w=-10,load_error_w=0,input_error_w=0,auxiliary_error_w=0,storage_error_w=0,other_error_w=0)
    assert a['nominal_required_suppression_w']==35

def test_auxiliary_input_reduces_suppression():
    a=loss_suppression_interval(auxiliary_delta_w=45,load_error_w=0,input_error_w=0,auxiliary_error_w=0,storage_error_w=0,other_error_w=0)
    assert a['nominal_required_suppression_w']==0

def test_conservation_torque():
    a=shaft_torque_requirements()
    assert abs(a['delta_torque_at_fixed_speed_nm']*a['omega_rad_s']-45)<1e-9

def test_torque_error_less_than_3_w():assert shaft_torque_requirements()['worst_case_power_error_w']<3

def test_10x_worse_torque_sensor():assert shaft_torque_requirements(sensor_abs_torque_error_nm=.1)['worst_case_power_error_w']>20

def test_uncertainty_without_probabilities():assert loss_suppression_interval()['confidence'] is None

def test_omega_receipt_has_no_false_physical_acceptance():
    r=run();assert not r['device_identified'] and not r['agda_kernel_verified']
