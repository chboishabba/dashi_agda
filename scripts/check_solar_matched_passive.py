"""Native matched endpoint policies; no asymptotic-prefix witness promotion."""
import numpy as np
from check_solar_spherical_reverse_integration import fixture
from solar_passive_campaign_bound import bound_layout

def run():
    mat,cfg,_,_=fixture(); n=len(cfg['row_keys'])
    cfg=dict(cfg,max_cycles=1,restoration_steps=0,incident_sqrt_W=[.2],
        heating_W=np.zeros((1,n)),period_s=.001,common_stage_atlas=True,sparse_operator=True)
    kin=dict(cfg['kinetics'],ionization_s_inv=[0.,0.]);cfg['kinetics']=kin
    policy=dict(removed_limit_m3=np.full((n,3),1e10),created_limit_m3=np.full((n,3),1e10),
        cooling_limit_J=np.full(n,1.),cooling_COP=np.full(n,2.),
        birth_velocity_m_s=np.zeros((n,3,3)),extra_actuator_work_J=0.,gross_paid_budget_J=1.)
    controlled=bound_layout(mat,cfg,[0],.04,max_boxes=1,restoration_mode='controlled',terminal_policy=policy)
    assert controlled['restoration_mode']=='controlled' and controlled['center_replays']==1
    assert controlled['failed_replays']==0 and len(controlled['mode_candidates'])==1
    asym=bound_layout(mat,dict(cfg,asymptotic_tail_probe_steps=64),[0],.04,max_boxes=1,restoration_mode='asymptotic')
    assert asym['failed_replays']==0 and asym['best_center_net_J'] is None
    assert not asym['mode_candidates'][0]['accepted']
    print(dict(status='MATCHED_PASSIVE_POLICY_PASS',controlled_upper_J=controlled['upper_candidate_J'],
        asymptotic_upper_J=asym['upper_candidate_J'],asymptotic_witness_admitted=False,physical_admission=False))
if __name__=='__main__':run()
