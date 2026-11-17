import sys, math
from pathlib import Path
from dataclasses import replace
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from v2_lc_recovery_tranche import LC,cycle,periodic,rotation_state,run

@pytest.mark.parametrize('phi',[0,0.2,1.2,math.pi/2,math.pi])
def test_rotation_preserves_energy(phi):
    a,b=rotation_state(2.,3.,phi)
    assert abs(a*a+b*b-13)<1e-12

@pytest.mark.parametrize('f',[0.,.25,.5,.8,1.])
def test_passive_energy_partition(f):
    p=LC(extraction_fraction=f)
    r=cycle(p,.25,1.)
    assert abs(r['energy_residual_j'])<1e-12
    assert r['line_loss_j']>=0 and r['converter_loss_j']>=0

@pytest.mark.parametrize('f',[.1,.35,.7])
def test_unique_periodic_storage(f):
    p=LC(extraction_fraction=f)
    r=periodic(p)
    assert r['steady_state_identifiable']
    assert abs(r['steady']['stored_delta_j'])<1e-12
    assert r['period_multiplier']<1

@pytest.mark.parametrize('bad',[-.01,1.01])
def test_unsafe_recovery_rejected(bad):
    with pytest.raises(ValueError): cycle(LC(converter_efficiency=bad),0.)

def test_controller_high_loss_reverses_gain():
    x=run()['cases']
    assert x['enhanced_extraction']['result']['steady']['useful_net_j']>x['ordinary_lossy_clamp']['result']['steady']['useful_net_j']
    assert x['high_overhead']['result']['steady']['useful_net_j']<x['ordinary_lossy_clamp']['result']['steady']['useful_net_j']

def test_source_stopped_discharge():
    p=LC(external_kick_j=0.)
    initial=.4
    r=cycle(p,initial)
    assert r['stored_final_j']<initial and r['useful_net_j']<initial
    assert abs(r['energy_residual_j'])<1e-12

def test_without_extraction_nonunique_when_lossless():
    assert not periodic(LC(passive_ring_survival=1,extraction_fraction=0))['steady_state_identifiable']
