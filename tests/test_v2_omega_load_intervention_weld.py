import sys, pathlib, math
from dataclasses import replace
from fractions import Fraction as F
import pytest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'scripts'))
from v2_omega_load_intervention_weld import *

@pytest.mark.parametrize('l,r',list(product((0,1),repeat=2)))
def test_four_arms_exact_balance(l,r):
    p=arm(l,r); assert p.motor_residual==p.gen_residual==p.whole_residual==0

@pytest.mark.parametrize('l,r',list(product((0,1),repeat=2)))
def test_all_four_arms_stationary(l,r):arm(l,r).validate(allow_depletion=False)

@pytest.mark.parametrize('l,r',list(product((0,1),repeat=2)))
def test_all_ports_positive(l,r):
    p=arm(l,r); assert min(p.motor_loss,p.generator_loss,p.shaft_to_generator,p.electric_load,p.other_output)>=0

def test_constant_motor_input_does_not_fix_shaft():
    a,b=arm(0,0),arm(1,0)
    assert a.motor_input==b.motor_input==286 and b.shaft_to_generator-a.shaft_to_generator==45

def test_rise_in_shaft_means_reduction_motor_loss():
    a,b=arm(0,0),arm(1,0);assert b.motor_loss-a.motor_loss==-45

def test_same_generator_loss_on_unrecovered_load():
    assert arm(0,0).generator_loss==arm(1,0).generator_loss

def test_recovery_interaction_is_not_energy_source():
    r=contrasts()
    assert r['interaction_w']['electric_load']=='7'
    assert r['interaction_w']['generator_loss']=='-7'
    assert r['whole_interaction_residual_w']=='0'

def test_auxiliary_is_explicit():assert arm(1,1).auxiliary_input==F('0.4')

def test_recovery_offload_aux_absorbed():assert arm(0,1).electric_load==0 and arm(0,1).generator_loss==F('80.4')

def test_all_counterworlds_exact():
    world=alternative_45w_counterworlds();assert len(world['alternatives'])==5

def test_loss_suppression_counterworld():
    w=alternative_45w_counterworlds()['alternatives']['reduced_generator_loss']
    assert w['generator_loss']=='35' and w['shaft_to_generator']=='200'

def test_increased_shaft_counterworld():
    w=alternative_45w_counterworlds()['alternatives']['increased_shaft_at_constant_motor_input']
    assert w['shaft_to_generator']=='245' and w['motor_loss']=='41'

def test_storage_depletion_counterworld():
    w=alternative_45w_counterworlds()['alternatives']['depleting_rotor_or_other_storage']
    assert w['rotor_storage_rate']=='-45'

def test_storage_counterworld_not_stationary():
    w=Ports(Q(286),Q(0),Q(200),Q(45),Q(120),Q(86),Q(80),rotor_storage_rate=Q(-45))
    with pytest.raises(ValueError,match='storage'):w.validate(allow_depletion=False)

def test_hidden_other_output_counterworld():
    w=alternative_45w_counterworlds()['alternatives']['displaced_other_output']
    assert w['other_output']=='75'

def test_unmetered_aux_counterworld():
    w=alternative_45w_counterworlds()['alternatives']['unmeasured_auxiliary']
    assert w['auxiliary_input']=='45'

def test_double_count_shaft_detected():
    p=arm(1,0)
    assert p.whole_residual==0
    assert p.motor_input+p.shaft_to_generator != p.electric_load+p.other_output+p.motor_loss+p.generator_loss

def test_nonphysical_negative_loss_rejected():
    with pytest.raises(ValueError):replace(arm(0,0),motor_loss=F(-1)).validate()

def test_fake_extra_power_rejected():
    with pytest.raises(ValueError):replace(arm(0,0),electric_load=F(1)).validate()

def test_binary_interventions_enforced():
    with pytest.raises(ValueError):arm(2,0)

def test_torque_power_correspondence():
    r=motor_generator_intervention_signature()
    assert math.isclose(r['shaft_torque_change_nm']*2*math.pi*2354/60,45)

def test_metered_motor_watts_stay_flat_even_shaft_rises():
    r=motor_generator_intervention_signature();assert r['motor_electrical_change_w']==0 and r['shaft_change_w']==45

def test_mechanical_measurement_independent():
    a=sensor_discriminator();assert a['basic_rank']==1 and a['basic_nullity']==4

def test_complete_measurement_rank():
    a=sensor_discriminator();assert a['full_rank']==5 and a['full_nullity']==0

def test_duplicate_meter_no_shaft_information():
    import sympy as s
    a=sensor_discriminator();b=s.Matrix([[1,-1,-1,-1,0],a['sensor_rows']['duplicate_electrical_meter']]);assert b.rank()==1

def test_interaction_signed_error_interval():
    r=worst_case_interaction_error({'00':1,'01':1,'10':1,'11':1})
    assert r['interval_w']==['3','11'] and r['sign_certified']

def test_interaction_bad_precision_not_certified():
    r=worst_case_interaction_error(dict.fromkeys(('00','01','10','11'),2))
    assert r['interval_w']==['-1','15'] and not r['sign_certified']

def test_interaction_zero_bound_exact():
    r=worst_case_interaction_error(dict.fromkeys(('00','01','10','11'),0))
    assert r['interval_w']==['7','7']

def test_drift_is_not_protected_by_interval():
    r=worst_case_interaction_error({'00':1,'01':1,'10':1,'11':1});assert r['confidence'] is None

def test_invalid_error_structure_rejected():
    with pytest.raises(ValueError):worst_case_interaction_error({'00':1})

def test_negative_error_rejected():
    with pytest.raises(ValueError):worst_case_interaction_error({'00':0,'01':-1,'10':0,'11':0})

def test_json_receipt_does_not_claim_device_proof():
    r=run();assert 'not measured' in r['status'] and r['agda_kernel']=='NOT RUN'
