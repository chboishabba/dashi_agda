"""Original native matched controlled/asymptotic prefix and four-world gates."""
import numpy as np
from solar_synthetic_fixture import fixture
from solar_passive_campaign_bound import bound_layout
from solar_controlled_terminal_return import controlled_four_worlds


def run():
    m,c,_,_=fixture();n=len(m[0]);c=dict(c,max_cycles=1,restoration_steps=0,incident_sqrt_W=[.2],heating_W=np.zeros((1,n)),period_s=.001,common_stage_atlas=True,sparse_operator=True,kinetics=dict(c['kinetics'],ionization_s_inv=[0.,0.]))
    p=dict(removed_limit_m3=np.full((n,3),1e10),created_limit_m3=np.full((n,3),1e10),
        cooling_limit_J=np.full(n,1.),cooling_COP=np.full(n,2.),birth_velocity_m_s=np.zeros((n,3,3)),extra_actuator_work_J=0.,gross_paid_budget_J=1.)
    a=bound_layout(m,c,[0],.04,max_boxes=1,restoration_mode='controlled',terminal_policy=p)
    b=bound_layout(m,dict(c,asymptotic_tail_probe_steps=64),[0],.04,max_boxes=1,restoration_mode='asymptotic')
    assert a['failed_replays']==b['failed_replays']==0 and len(a['mode_candidates'])==len(b['mode_candidates'])==1
    assert a['best_center_net_J'] is None and b['best_center_net_J'] is None and not b['mode_candidates'][0]['accepted']
    w=controlled_four_worlds(m,dict(c,heating_W=np.full((1,n),.005)),p)
    assert w['controlled_interaction_J'] is None
    for k,v in w['worlds'].items():
        assert 'rejected' not in v and max(v['return_residual'][1:])==0.
        if k.startswith('source'):assert v['controlled_tolerance_net_J'] is None and v['return_residual'][0]>1e-12
        else:assert v['controlled_tolerance_net_J']<=0
    print(dict(status='NATIVE_MATCHED_RETURN_PASS',controlled_upper_J=a['upper_candidate_J'],asymptotic_prefix_upper_J=b['upper_candidate_J'],
        four_worlds={k:dict(net_J=v['controlled_tolerance_net_J'],return_residual=v['return_residual'],gross_paid_J=v['controlled_return']['gross_paid_J']) for k,v in w['worlds'].items()},interaction_admitted=False,physical_admission=False))
if __name__=='__main__':run()
