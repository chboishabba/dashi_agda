"""Full-horizon passive reflection enclosure for the actual split Cayley map.

For a load box, compare with one center replay. All population and thermal
events are identical at zero heating, and their current map is affine
nonexpansive (surviving population divided by sqrt(old*new)). The local
Cayley maps are contractions; remote skew stages are isometries. The
center midpoint supplies a sharp load perturbation bound without assuming
the field resets. Real-arithmetic inequality; floating implementation is
a numerical enclosure candidate, not outward-rounded certification.
"""
import numpy as np
import heapq

def reflection_enclosure(trace,center,lo,hi,dt,port,source_edge,fixed_terminal=False):
    center,lo,hi=map(lambda v:np.asarray(v,float),(center,lo,hi))
    assert np.all(lo<=center) and np.all(center<=hi) and np.all(lo>=0)
    assert dt>0 and port>0
    radius=np.maximum(center-lo,hi-center)
    error=0.; lower=0.; per_step=[]
    for step in trace:
        delta=np.zeros_like(radius) if fixed_terminal and step['terminal'] else radius
        mid=np.asarray(step['edge_midpoint'],float)
        assert mid.shape==radius.shape
        perturb=dt*delta*abs(mid)
        # The source coordinate is a scalar site. Difference of its
        # midpoint is bounded by incoming state error + half local defect.
        amplitude_error=port*(error+perturb[source_edge]/2)
        r=max(0.,abs(step['reflected'])-amplitude_error)
        lower+=dt*r*r
        error+=np.linalg.norm(perturb)
        per_step.append(dict(reflection_lower_J=dt*r*r,state_error_radius=float(error)))
    return dict(reflection_lower_J=float(lower),final_error_radius=float(error),steps=per_step)

def bound_layout(material,cfg,ids,budget,max_boxes=8):
    from solar_spherical_cycle import cycle,geometry
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'])
    ids=np.asarray(ids,int); assert len(ids)>0 and len(set(ids))==len(ids)
    assert np.all((ids>=0)&(ids<ne)) and budget>=0 and max_boxes>=1
    dt=cfg['period_s']/len(cfg['incident_sqrt_W'])
    incident=cfg['max_cycles']*dt*np.sum(np.asarray(cfg['incident_sqrt_W'])**2)
    ceiling=float(incident-cfg['max_cycles']*cfg['auxiliary_J'])
    port=float(cfg['source_coupling_sqrt_inv_s']); edge=int(cfg['source_edge'])
    seq=0; queue=[]; replay_count=0; failed=0; best=None
    def box(lo,hi,parent_upper):
        nonlocal seq,replay_count,failed,best
        if lo.sum()>budget: return
        # Tighten each coordinate by the others' minimum feasible allocation.
        hi=np.minimum(hi,budget-(lo.sum()-lo))
        if np.any(hi<lo):return
        mid=(lo+hi)/2; slack=budget-lo.sum()
        if mid.sum()>budget:mid=lo+(mid-lo)*slack/max((mid-lo).sum(),1e-300)
        cc=dict(cfg,fixed_horizon=True,retain_sensitivity=True,retain_history=False,
                heating_W=np.zeros_like(cfg['heating_W']),load_rate_s_inv=mid)
        upper=parent_upper
        try:
            replay_count+=1; out=cycle(material,cc)
            en=reflection_enclosure(out['sensitivity_trace'],mid,lo,hi,dt,port,edge,'terminal_load_rate_s_inv' in cfg)
            upper=min(upper,ceiling-en['reflection_lower_J'])
            score=out['strict_campaign_net_J']
            if score is not None and np.isfinite(score):best=score if best is None else max(best,score)
        except (ValueError,AssertionError,np.linalg.LinAlgError,FloatingPointError):
            failed+=1 # retain parent upper; never discard failed region
        seq+=1; heapq.heappush(queue,(-upper,seq,lo,hi))
    lo=np.zeros(ne); hi=np.zeros(ne); hi[ids]=budget
    box(lo,hi,ceiling)
    for _ in range((max_boxes-1)//2):
        if not queue:break
        neg,_,lo,hi=heapq.heappop(queue)
        j=int(np.argmax(hi-lo))
        if hi[j]==lo[j]:
            seq+=1; heapq.heappush(queue,(neg,seq,lo,hi)); break
        m=(lo[j]+hi[j])/2
        h=hi.copy(); h[j]=m
        l=lo.copy(); l[j]=m
        box(lo,h,-neg);box(l,hi,-neg)
    upper=max((-item[0] for item in queue),default=ceiling)
    if best is not None and best>upper+1e-8*max(1.,abs(upper)):
        raise ArithmeticError('candidate enclosure violated by replay')
    return dict(upper_candidate_J=float(upper),best_center_net_J=best,
                center_replays=replay_count,failed_replays=failed,remaining_boxes=len(queue),
                gap_J=None if best is None else float(upper-best),
                outward_rounding_certified=False,physical_admission=False)

def fixtures():
    # scalar source stage followed by a lossless two-coordinate rotation.
    from fractions import Fraction as F
    h=F(1,3); p=F(1); a=[F(1),F(-1,2),F(0)]
    def run(l):
        x,y=F(0),F(0); trace=[]; reflected=F(0)
        for inc in a:
            mid=(x+h*inc*p)/(1+h*(l+p*p)/2)
            x=2*mid-x; r=p*mid-inc; reflected+=h*r*r
            trace.append(dict(terminal=False,edge_midpoint=[float(mid),float(y)],reflected=float(r)))
            x,y=(3*x-4*y)/5,(4*x+3*y)/5
        return trace,reflected
    tr,_=run(F(1,2))
    b=reflection_enclosure(tr,[.5,0],[.4,0],[.6,0],float(h),1.,0)
    for j in range(21):
        _,r=run(F(40+j,100))
        assert float(r)+1e-14>=b['reflection_lower_J']
    return dict(cases=21,reflection_lower_J=b['reflection_lower_J'])
if __name__=='__main__':
    import json
    print(json.dumps(fixtures(),indent=2))
