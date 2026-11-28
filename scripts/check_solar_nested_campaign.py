"""Native 24->576 tetrahedral nested campaign, not a physical port identity."""
import numpy as np
from check_solar_spherical_reverse_integration import fixture
from solar_spherical_material_weld import assembly_mesh
from solar_nested_cochain_refinement import nested_cochains
from solar_nested_campaign import compare_nested

def run(jets=False):
    mat,cfg,dh,dl=fixture()
    cfg=dict(cfg,max_cycles=1,restoration_steps=0,incident_sqrt_W=[.2],
        heating_W=np.asarray(cfg['heating_W'])[:1],period_s=.001,common_stage_atlas=True)
    xyz,s,_,_=assembly_mesh(tuple(cfg['radii_m']),cfg['angular_level'])
    bundle=nested_cochains(xyz,s);fine_edges=len(bundle['simplices'][1])
    edge=int(bundle['restriction'][1].getrow(int(cfg['source_edge'])).indices[0])
    load=np.zeros(fine_edges);load[edge]=.04
    ports=dict(source_edge=edge,source_coupling_sqrt_inv_s=.2,load_rate_s_inv=load,
        return_atol=[1e-12,1e-8,1e-8,1e-12])
    fine_dl=np.zeros_like(load);fine_dl[edge]=.08
    out=compare_nested(mat,cfg,ports,dh[:1] if jets else None,dl if jets else None,fine_dl if jets else None)
    assert out['geometry']['coarse_size']==314 and out['geometry']['fine_size']==7140
    assert out['base_reopen_error']<1e-12
    assert out['fine']['sparse_operator']
    step=out['fine']['signed_evolution_residual_trace'][0]
    assert step['endpoint_error']<=step['error_bound_candidate']+1e-10
    assert not out['geometry']['physical_port_equivalence_admitted']
    if jets:assert out['jet_reopen']['reconstruction_error']<1e-12
    print(dict(status='NESTED_NATIVE_CAMPAIGN_PASS',jets=jets,field_error=step['endpoint_error'],
        field_bound=step['error_bound_candidate'],receiver_bound=step['work_error_bound_candidate_J'],
        base_reopen_error=out['base_reopen_error'],physical_admission=False))
if __name__=='__main__':run()
