"""Independent synthetic and symbolic checks; physical V2 identity NOT proven."""
import importlib.util
from pathlib import Path
import sys
import math

ROOT=Path(__file__).resolve().parents[1]
SCRIPT=ROOT/'scripts/check_reluctance_phase_symmetry_maxcut.py'
spec=importlib.util.spec_from_file_location('phase_symmetry_maxcut',SCRIPT)
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)


def test_exact_phase_cancellation():
    r=mod.exact_replicated_phase_cancellation()
    assert r['mean_copper_loss']=='R*S'
    assert r['nonlinear_multicoil_coenergy']=='formal symbolic identity = 0'


def test_phase_penalty_intervals():
    x=mod.phase_penalty_thresholds()
    for n,alpha in ((3,.150),(6,.015),(9,.005)):
        interval=x[f'phase_{n}']
        assert alpha>=interval['alpha_lower']
        assert interval['alpha_upper'] is None or alpha<=interval['alpha_upper']
    for n,alpha in ((4,.05),(5,.03),(7,.01)):
        ranks=sorted((mod.MODEL.ideal_phase_cover(k)['constant_torque_current_sq_multiplier']+alpha*k,k) for k in range(3,13))
        assert ranks[0][1]==n

def test_symmetry_under_three_distinct_pulse_shapes():
    r=mod.assess_normalized_phase_invariance()
    assert len(r['symmetry_cases'])==3
    for x in r['symmetry_cases']:
        assert x['mean_shaft_braking_range_w']<2e-3
        assert x['ideal_export_spread_w']<2e-3
        assert x['copper_spread_w']<2e-3
        assert abs(x['bus_drop_3_to_9_w']-mod.MODEL.Model().switch_overhead_w_per_phase*6)<2e-3


def test_perfect_regulator_changes_loss_not_energy_source():
    r=mod.ideal_regulator_sensitivity()
    cases=r['cases']
    assert cases[0]['bus_w']<cases[-1]['bus_w']
    assert math.isclose(cases[-1]['bus_w'],cases[-1]['coil_ideal_w'],abs_tol=1e-8)
    assert cases[-1]['coil_ideal_w']<62.5


def test_claims_and_attribution_fail_closed():
    r=mod.run()
    assert 'not attributed circuit disclosure' in r['author_role']
    assert len(r['models_not_identical'])==3
    assert len(r['open_physical_producers'])==5