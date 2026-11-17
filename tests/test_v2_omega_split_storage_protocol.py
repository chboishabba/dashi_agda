from dataclasses import replace
from fractions import Fraction as Q
import csv, importlib.util, sys
from pathlib import Path
import pytest
BASE=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('split',BASE/'scripts/v2_omega_split_storage_protocol.py')
split=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=split;spec.loader.exec_module(split)

def row(arm,b=0,seq=0):
    # Motor 286 -> shaft 200 + motor heat 86; shaft 200 -> generator heat 200.
    v={k:'0' for k in split.COLS};v.update(block=str(b),sequence=str(seq),arm=arm,duration_s='1',
    motor_input_w='286',shaft_transfer_w='200',motor_loss_w='86',generator_loss_w='200',
    motor_store_before_j='100',motor_store_after_j='100',
    generator_store_before_j='200',generator_store_after_j='200')
    return v

def fixtures():
    rows=[]
    for z in split.design(4):
        v=row(z['arm'],z['block'],z['sequence']);rows.append(split.Sample.parse(v))
    return rows

def replace_value(x,k,v):return replace(x,values={**x.values,k:Q(v)})

def test_balanced():assert len(split.design(4))==32 and all(len([r for r in fixtures() if r.arm==a])==8 for a in split.ARM_IDS)
def test_no_original_claim():assert split.audit(fixtures())['original_v2_verified'] is False
def test_exact_balances():assert all(all(v==0 for v in x.residuals().values()) for x in fixtures())
def test_storage_split_detects_hidden_motor_discharge():
    xs=fixtures();x=xs[0]
    # Shaft 201 W with motor input 286 and motor heat 86; 1 J motor energy discharged.
    x=replace_value(x,'shaft_transfer_w',201)
    x=replace_value(x,'motor_store_after_j',99)
    # Generator consumes extra 1 W as dissipation: whole ledger still closes.
    x=replace_value(x,'generator_loss_w',201)
    assert x.residuals()=={'motor':0,'generator':0,'whole':0}
    with pytest.raises(ValueError,match='motor storage'):split.audit([x]+xs[1:])
def test_stationary_false_permits_measured_depletion():
    xs=fixtures();x=xs[0]
    for k,v in [('shaft_transfer_w',201),('motor_store_after_j',99),('generator_loss_w',201)]:x=replace_value(x,k,v)
    assert split.audit([x]+xs[1:],stationary=False)['original_v2_verified'] is False

def test_missing_generator_store_rejected():
    x=row('00');del x['generator_store_after_j']
    with pytest.raises(ValueError,match='schema'):split.Sample.parse(x)

def test_missing_motor_store_rejected():
    x=row('00');x['motor_store_after_j']=''
    with pytest.raises(ValueError,match='missing'):split.Sample.parse(x)

def test_broken_motor_balance():
    xs=fixtures();xs[0]=replace_value(xs[0],'motor_input_w',287)
    with pytest.raises(ValueError,match='motor signed'):split.audit(xs)

def test_broken_generator_balance():
    xs=fixtures();xs[0]=replace_value(xs[0],'generator_loss_w',199)
    with pytest.raises(ValueError,match='generator signed'):split.audit(xs)

def test_thermal_sensor_cannot_be_imputed():
    x=row('00');x['motor_loss_w']=''
    with pytest.raises(ValueError,match='missing'):split.Sample.parse(x)

def test_nonzero_load_factorial_interaction():
    xs=fixtures();out=[]
    for x in xs:
        # Increased output +7 W ONLY in 11, offset by generator loss decrease.
        if x.arm=='11':
            x=replace_value(x,'load_output_w',7)
            x=replace_value(x,'generator_loss_w',193)
        out.append(x)
    result=split.audit(out)
    assert all(Q(str(y['interactions_w']['load_output_w']))==7 for y in result['blocks'])
    assert all(Q(str(y['interactions_w']['generator_loss_w']))==-7 for y in result['blocks'])

def test_withheld_auxiliary_is_not_ignored():
    xs=fixtures();xs[0]=replace_value(xs[0],'aux_input_w',1)
    with pytest.raises(ValueError,match='generator signed'):split.audit(xs)

def test_nonpalindromic_schedule_rejected():
    xs=fixtures();xs[0]=replace(xs[0],sequence=1)
    with pytest.raises(ValueError,match='positions'):split.audit(xs)

def test_negative_uncertainty_rejected():
    x=row('00');x['motor_loss_err_w']='-1'
    with pytest.raises(ValueError,match='negative'):split.Sample.parse(x)

def test_missing_zero_is_not_assumed():
    x=row('00');x['aux_input_w']=''
    with pytest.raises(ValueError,match='missing'):split.Sample.parse(x)

def test_template_unfilled(tmp_path):
    p=tmp_path/'blank.csv';split.template(p,4)
    with p.open() as f:lines=list(csv.DictReader(f))
    assert len(lines)==32 and lines[0]['motor_input_w']==''
    with pytest.raises(ValueError,match='missing'):split.load(p)

def test_uncertainty_not_significant():
    xs=fixtures();out=[]
    for x in xs:
        if x.arm=='11':
            x=replace_value(x,'load_output_w',7);x=replace_value(x,'generator_loss_w',193)
        x=replace_value(x,'load_output_err_w',2)
        out.append(x)
    assert not split.audit(out)['blocks'][0]['load_interaction_sign_certified']

def test_positive_error_interval_certifies_sign():
    xs=fixtures();out=[]
    for x in xs:
        if x.arm=='11':
            x=replace_value(x,'load_output_w',7);x=replace_value(x,'generator_loss_w',193)
        x=replace_value(x,'load_output_err_w',Q(1,4))
        out.append(x)
    assert split.audit(out)['blocks'][0]['load_interaction_sign_certified']

def test_motor_storage_can_charge():
    xs=fixtures();x=xs[0]
    # Shaft reduces 1 W; motor store charges 1 J.
    x=replace_value(x,'shaft_transfer_w',199)
    x=replace_value(x,'motor_store_after_j',101)
    x=replace_value(x,'generator_loss_w',199)
    assert x.residuals()=={'motor':0,'generator':0,'whole':0}
    with pytest.raises(ValueError,match='motor storage'):split.audit([x]+xs[1:])

def test_nonfinite_rejected():
    x=row('00');x['motor_input_w']='nan'
    with pytest.raises(ValueError,match='nonfinite'):split.Sample.parse(x)
