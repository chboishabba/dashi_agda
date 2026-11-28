"""Native exact-input asymptotic return and fixed-heat dominance (synthetic)."""
from fractions import Fraction as F
import numpy as np
from solar_synthetic_fixture import fixture
from solar_exact_tail_endpoint import compare_fixed_heat,tolerance_clock
from solar_spherical_geometry import geometry


def run():
    m,c,_,_=fixture();rows,neutral,D,g,axis=m;n=len(rows);m=(rows,neutral,np.zeros_like(D),g,axis)
    c=dict(c,max_cycles=1,restoration_steps=0,incident_sqrt_W=[.2],period_s=.001,
        heating_W=np.full((1,n),.005),common_stage_atlas=True,sparse_operator=True,
        kinetics=dict(c['kinetics'],ionization_s_inv=[0.,0.],formation_J_per_particle=[1e-19,2e-19,3e-19]))
    out=compare_fixed_heat(m,c,.04);assert out['comparison_admitted'] and out['fixed_heat_active_dominated']
    assert not out['all_active_heat_paths_compared'] and not out['physical_admission']
    a=out['active'];b=out['passive'];assert a['exact_finite_split_asymptotic_return'] and b['exact_finite_split_asymptotic_return']
    vol,_,_,_=geometry(c['radii_m'],c['angular_level']);clock=tolerance_clock(a['prefix'],a['tail_policy'],m,c,vol,c['return_atol'])
    rem=clock['endpoint_remainder'];assert all(F(rem[k])<=F(float(v)) for k,v in zip(('field_norm_upper','population_norm_upper','pool_norm_upper','thermal_norm_upper'),c['return_atol']))
    print(dict(status='EXACT_TAIL_ENDPOINT_PASS',active_upper_J=float(F(out['active_upper_J'])),passive_lower_J=float(F(out['passive_lower_J'])),active_minus_passive_upper_J=float(F(out['active_minus_passive_upper_J'])),
        block=a['tail_policy']['reference']['certificate'],tail_seconds=float(F(clock['sufficient_seconds_exact'])),
        remaining_work_upper_J=float(F(rem['additional_net_interval_J'][1])),physical_admission=False))
if __name__=='__main__':run()
