import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from check_v2_maxcut import findings, partition, storage_required, minimum_inertia_for_fractional_speed_drop
from fractions import Fraction

def test_loss_compensation_conservative():
    assert partition(Fraction(286), Fraction(45), Fraction(241))
    assert not partition(Fraction(286), Fraction(45), Fraction(286))

def test_storage_windows():
    assert [storage_required(t) for t in (10,30,60)] == [450,1350,2700]

def test_inertia_scales_duration():
    assert abs(minimum_inertia_for_fractional_speed_drop(30)/minimum_inertia_for_fractional_speed_drop(10)-3)<1e-12

def test_attribution_ceiling():
    x=findings()
    assert x['evidence_gaps']['v2_pulse_topology_from_supplied_transcript']=='not-established'
    assert x['evidence_gaps']['simultaneous_shaft_torque']=='not-available'