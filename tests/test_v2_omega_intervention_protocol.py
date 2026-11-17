from fractions import Fraction as F
import csv
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from v2_omega_intervention_protocol import (Run,COLUMNS,make_schedule,measured_blocks,assess,write_template,load_csv)
from v2_omega_load_intervention_weld import arm


def fixture(blocks=2,err=F(0),drift=F(0)):
    out=[]
    for row in make_schedule(blocks):
        p=arm(int(row['arm'][0]),int(row['arm'][1]))
        # a common additive time-linear sensor bias cancels in the contrast,
        # but remains identifiable in the energy balance unless a matching
        # (physically independent!) meter measures the balancing term.
        time=F(row['sequence'])
        inp=dict(row,duration_s=F(10),motor_w=p.motor_input+drift*time,
           aux_w=p.auxiliary_input,load_w=p.electric_load,
           other_w=p.other_output, motor_loss_w=p.motor_loss+drift*time,
           generator_loss_w=p.generator_loss,shaft_w=p.shaft_to_generator,
           stored_before_j=F(100),stored_after_j=F(100))
        for k in COLUMNS:
            if k.endswith('_abs_error_w') or k=='storage_abs_error_j':inp[k]=err
        out.append(Run(**inp))
    return out

@pytest.mark.parametrize('blocks',[1,2,4,7])
def test_schedule_counts_and_symmetry(blocks):
    sch=make_schedule(blocks)
    assert len(sch)==blocks*8
    for b in range(blocks):
        group=[x for x in sch if x['block']==b]
        assert all(sum(x['sequence'] for x in group if x['arm']==arm)==7 for arm in ('00','01','10','11'))

@pytest.mark.parametrize('blocks',[1,2,4])
def test_exact_fixture_energy_and_interaction(blocks):
    result=assess(fixture(blocks))
    assert result['block_count']==blocks
    for x in result['blocks']:
        assert x['interaction_load_w']==7
        assert x['interaction_generator_loss_w']==-7
        assert x['interaction_shaft_w']==0
        assert x['whole_interaction_residual_w']==0

@pytest.mark.parametrize('d',[F('1/10'),F('2'),F('-7')])
def test_linear_clock_drift_cancels(d):
    result=assess(fixture(2,drift=d))
    assert all(x['interaction_load_w']==7 and x['interaction_motor_loss_w']==0 for x in result['blocks'])

def test_unbalanced_sequence_rejected():
    rows=fixture(1)
    r=rows[0]
    rows[0]=Run(**{**r.__dict__,'sequence':1})
    with pytest.raises(ValueError):assess(rows)

def test_missing_arm_rejected():
    with pytest.raises(ValueError):assess(fixture(1)[:-1])

def test_incomplete_csv_never_imputes():
    x={k:'' for k in COLUMNS}
    x.update(block='0',sequence='0',arm='00')
    with pytest.raises(ValueError):Run.from_row(x)

def test_unmatched_storage_rejected():
    rows=fixture(1)
    r=rows[0]; rows[0]=Run(**{**r.__dict__,'stored_after_j':F(140)})
    with pytest.raises(ValueError):assess(rows)

def test_auxiliary_meter_required_by_balance():
    rows=fixture(1)
    r=rows[0]; rows[0]=Run(**{**r.__dict__,'aux_w':r.aux_w+F(3)})
    with pytest.raises(ValueError):assess(rows)

def test_hidden_motor_power_cannot_be_accepted():
    rows=fixture(1)
    r=rows[0]; rows[0]=Run(**{**r.__dict__,'shaft_w':r.shaft_w+F(9)})
    with pytest.raises(ValueError):assess(rows)

def test_storage_loss_can_be_reported_when_explicit():
    rows=fixture(1)
    r=rows[0]; rate=F(2)
    rows[0]=Run(**{**r.__dict__, 'stored_after_j':r.stored_before_j+rate*r.duration_s,
       'generator_loss_w':r.generator_loss_w-rate})
    with pytest.raises(ValueError):assess(rows)
    assert assess(rows,require_storage_match=False)['block_count']==1

@pytest.mark.parametrize('err,sign',[('1/10',True),('2',False)])
def test_worst_case_meter_bound(err,sign):
    got=assess(fixture(1,err=F(err)))
    assert got['blocks'][0]['sign_identified']==sign

def test_template_has_no_fabricated_measurements(tmp_path):
    path=tmp_path/'measurements.csv';write_template(path,2)
    with path.open() as f:
        rows=list(csv.DictReader(f))
    assert len(rows)==16
    assert all(row['motor_w']=='' for row in rows)
    with pytest.raises(ValueError):load_csv(path)

def test_physical_negative_inventory_rejected():
    rows=fixture(1);r=rows[0];changed={**r.__dict__,'stored_before_j':F(-1)}
    with pytest.raises(ValueError):Run(**changed).validate()

@pytest.mark.parametrize('bad_field',['motor_abs_error_w','shaft_abs_error_w','storage_abs_error_j'])
def test_negative_uncertainty_rejected(bad_field):
    rows=fixture(1);r=rows[0]
    with pytest.raises(ValueError):Run(**{**r.__dict__,bad_field:F(-1)}).validate()

def test_robust_magnitude_matched_sign_vs_naive():
    rows=fixture(1,err=F('0.5'))
    assert assess(rows)['blocks'][0]['sign_identified']
    rows=fixture(1,err=F('2'))
    assert not assess(rows)['blocks'][0]['sign_identified']
