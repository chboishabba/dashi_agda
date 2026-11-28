"""Native complete synthetic forward campaign, no external measured input."""
import numpy as np
from fractions import Fraction
from solar_spherical_cycle import cycle,geometry,four_worlds
from solar_population_event import MASS,CHARGE

from solar_synthetic_fixture import fixture as original_fixture

def fixture():
    mat,cfg,_,_=original_fixture()
    return mat,dict(cfg,retain_sensitivity=True,common_stage_atlas=True)

def run():
    mat,cfg=fixture();a=cycle(mat,cfg);b=cycle(mat,dict(cfg,sparse_operator=True))
    assert a['history']==b['history'] and a['campaign_ledger']==b['campaign_ledger'] and a['sensitivity_trace']==b['sensitivity_trace']
    assert a['strict_campaign_net_J'] is None and a['analytic_return_geometry']['exact_original_return_obstructed']
    worlds=four_worlds(mat,dict(cfg,sparse_operator=True));assert worlds['strict_source_interaction_J'] is None
    print(dict(status='NATIVE_FORWARD_PASS',cells=len(cfg['row_keys']),steps=len(a['history']),dense_sparse_exact=True,
        balance_abs_J=a['campaign_ledger']['balance_abs_J'],campaign_net_J=a['campaign_net_J'],
        four_world_nets={k:v['campaign_net_J'] for k,v in worlds['worlds'].items()},strict_interaction_admitted=False))

def run_exact():
    mat,cfg=fixture();cfg=dict(cfg,max_cycles=1,restoration_steps=0,incident_sqrt_W=[.2,-.1],period_s=2e-4,
        heating_W=np.zeros((2,len(cfg['row_keys']))),sparse_operator=True,retain_stage_residuals=True,
        retain_nonfrozen_event_residuals=True,retain_sensitivity=False)
    out=cycle(mat,cfg);err=Fraction(out['exact_binary_field_solve_error']);ev=Fraction(out['exact_binary_event_error'])
    assert err>=ev>0 and out['exact_frozen_population_solve_error'] is None
    assert len(out['sensitivity_trace'])==2 and len(out['sensitivity_trace'][0]['midpoint_error'])==42
    assert not out['physical_material_rounding_enclosed']
    print(dict(status='NATIVE_NONFROZEN_BINARY_PASS',cells=len(cfg['row_keys']),field_error=float(err),event_error=float(ev),physical_admission=False))
if __name__=='__main__':
    import sys
    run_exact() if '--exact' in sys.argv else run()
