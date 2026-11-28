"""Direct exact passive receiver upper: rational scalar and native nonfrozen box."""
from fractions import Fraction as F
import numpy as np
from solar_passive_campaign_bound import rational_reflection_enclosure,bound_layout
from solar_synthetic_fixture import fixture

def run():
    h=F(1,3);p=F(1);inc=[F(1),F(-1,2),F(0)]
    def scalar(l):
        x=F(0);trace=[];work=F(0);reflected=F(0)
        for k,v in enumerate(inc):
            terminal=k==2;L=F(1,7) if terminal else l
            mid=(x+h*v*p)/(1+h*(L+p*p)/2);x=2*mid-x
            work+=h*L*mid*mid;reflected+=h*(p*mid-v)**2
            trace.append(dict(terminal=terminal,edge_midpoint=[str(mid)],midpoint_error=['0'],incident=str(v)))
        return trace,work,reflected
    tr,_,_=scalar(F(1,2))
    en=rational_reflection_enclosure(tr,[F(1,2)],[F(2,5)],[F(3,5)],h,p,0,True,[F(1,7)])
    for j in range(21):
        _,w,r=scalar(F(40+j,100))
        assert w<=F(en['direct_useful_upper_exact']) and r>=F(en['reflection_lower_exact'])
    m,c,_,_=fixture();n=len(m[0])
    c=dict(c,max_cycles=1,restoration_steps=0,incident_sqrt_W=[.2],heating_W=np.zeros((1,n)),
        period_s=.001,common_stage_atlas=True,sparse_operator=True,retain_stage_residuals=True,
        retain_nonfrozen_event_residuals=True,return_atol=[1.,1e8,1e8,1.])
    # Deliberately broad synthetic return allowances exercise the box upper,
    # not physical restoration. Nonzero formation/recovery exercises paid work.
    c['kinetics']=dict(c['kinetics'],formation_J_per_particle=[1e-19,2e-19,3e-19],chemical_recovery_efficiency=.5)
    o=bound_layout(m,c,[0],.04,max_boxes=3)
    assert o['failed_replays']==0 and o['remaining_boxes']==2 and not o['unresolved_upper']
    assert o['upper_candidate_J'] is not None and o['best_center_net_J'] is not None
    assert o['best_center_net_J']<=o['upper_candidate_J']
    assert len(o['rational_trace_candidates'])==3 and all(v['direct_net_upper_exact'] is not None for v in o['rational_trace_candidates'])
    print(dict(status='DIRECT_PASSIVE_BINARY_PASS',rational_scalar_cases=21,center_replays=o['center_replays'],
        upper_J=o['upper_candidate_J'],best_candidate_J=o['best_center_net_J'],physical_admission=False))
if __name__=='__main__':run()
