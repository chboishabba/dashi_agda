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

def rational_reflection_enclosure(trace,center,lo,hi,dt,port,source_edge,fixed_terminal=False):
    """Exact rational enclosure conditional on common binary operator history.

    Midpoint errors must include accumulated center solve defects. A separate
    material coefficient enclosure is required for continuum or uncertain inputs.
    """
    from fractions import Fraction as F
    def q(x): return F(x) if isinstance(x,(str,F,int)) else F(float(x))
    center,lo,hi=([q(v) for v in a] for a in (center,lo,hi))
    h,p=q(dt),q(port)
    assert h>0 and p>0 and len(center)==len(lo)==len(hi)
    assert all(0<=l<=m<=u for l,m,u in zip(lo,center,hi))
    radius=[max(m-l,u-m) for l,m,u in zip(lo,center,hi)]
    error=F(0); lower=F(0)
    for step in trace:
        mid=list(map(q,step['edge_midpoint']))
        eps=list(map(q,step['midpoint_error']))
        assert len(mid)==len(eps)==len(radius) and all(e>=0 for e in eps)
        delta=[F(0)]*len(radius) if fixed_terminal and step['terminal'] else radius
        perturb=[h*d*(abs(m)+e) for d,m,e in zip(delta,mid,eps)]
        # Reconstruct the signed reference from the input port and midpoint,
        # rather than trusting the rounded reflected amplitude.
        # Floating midpoint averaging itself needs an additional error bound.
        inc=q(step['incident'])
        r=p*mid[source_edge]-inc
        allowance=p*(error+perturb[source_edge]/2+eps[source_edge])
        lower+=h*max(F(0),abs(r)-allowance)**2
        error+=sum(perturb)
    return dict(reflection_lower_exact=str(lower),parameter_error_exact=str(error),
                scope='conditional rational trace enclosure; coefficient and midpoint rounding premises required')

def rational_restoration_exclusion(field,center_error,parameter_error,atol):
    """Exact triangle-inequality exclusion on the binary frozen-event chart."""
    from fractions import Fraction as F
    q=lambda v:F(v) if isinstance(v,(str,F,int)) else F(float(v))
    e,p,t=map(q,(center_error,parameter_error,atol))
    if min(e,p,t)<0: raise ValueError('negative error/return allowance')
    norm2=sum((q(v)**2 for v in field),F(0))
    threshold=(e+p+t)**2
    return dict(excluded=norm2>threshold,center_norm2=str(norm2),
                squared_return_radius=str(threshold))

def bound_layout(material,cfg,ids,budget,max_boxes=8,restoration_mode='finite_tolerance',terminal_policy=None):
    from solar_spherical_cycle import cycle,geometry
    if restoration_mode not in ('finite_tolerance','controlled','asymptotic'):
        raise ValueError('unknown restoration policy')
    if (restoration_mode=='controlled') != (terminal_policy is not None):
        raise ValueError('controlled route requires its actual shared terminal actuator policy')
    if restoration_mode=='asymptotic' and 'asymptotic_tail_probe_steps' not in cfg:
        raise ValueError('asymptotic route requires source-off tail receipt')
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'],int(cfg.get('nested_depth',0)))
    ids=np.asarray(ids,int); assert len(ids)>0 and len(set(ids))==len(ids)
    if 'terminal_load_rate_s_inv' in cfg:
        t=np.asarray(cfg['terminal_load_rate_s_inv'],float)
        if t.shape!=(ne,) or np.any(t<0) or t.sum()>budget or not set(np.flatnonzero(t))<=set(ids):
            raise ValueError('terminal receiver outside matched layout/resource budget')
    assert np.all((ids>=0)&(ids<ne)) and budget>=0 and max_boxes>=1
    dt=cfg['period_s']/len(cfg['incident_sqrt_W'])
    incident=cfg['max_cycles']*dt*np.sum(np.asarray(cfg['incident_sqrt_W'])**2)
    ceiling=float(incident-cfg['max_cycles']*cfg['auxiliary_J'])
    port=float(cfg['source_coupling_sqrt_inv_s']); edge=int(cfg['source_edge'])
    seq=0; queue=[]; replay_count=0; failed=0; best=None
    rational_candidates=[]; restoration_exclusions=[]; mode_candidates=[]
    from fractions import Fraction as F
    exact_ceiling=None
    if cfg.get('retain_stage_residuals',False):
        # Binary64 input chart, exact rational accounting of the incident
        # source amplitude squares and auxiliary tariff. No claim of exact
        # physical source provenance or material assembly rounding.
        h=F(float(dt)); exact_ceiling=int(cfg['max_cycles'])*(
            sum((h*F(float(a))**2 for a in cfg['incident_sqrt_W']),F(0))
            -F(float(cfg['auxiliary_J'])))
    def box(lo,hi,parent_upper):
        nonlocal seq,replay_count,failed,best
        # Exact mode must not remove a feasible binary-chart box using
        # rounded sums or rounded upper-face tightening. An infeasible
        # center can still enclose the whole box, but cannot be a witness.
        if exact_ceiling is not None:
            B=F(float(budget))
            if sum((F(float(v)) for v in lo),F(0))>B: return
            mid=lo+(hi-lo)/2
            center_feasible=sum((F(float(v)) for v in mid),F(0))<=B
        else:
            if lo.sum()>budget: return
            hi=np.minimum(hi,budget-(lo.sum()-lo))
            if np.any(hi<lo):return
            mid=(lo+hi)/2; slack=budget-lo.sum()
            if mid.sum()>budget:mid=lo+(mid-lo)*slack/max((mid-lo).sum(),1e-300)
            center_feasible=bool(mid.sum()<=budget)
        if np.any(mid<lo) or np.any(mid>hi):
            raise ArithmeticError('invalid box center')
        cc=dict(cfg,fixed_horizon=True,retain_sensitivity=True,retain_history=exact_ceiling is not None,
                heating_W=np.zeros_like(cfg['heating_W']),load_rate_s_inv=mid)
        upper=parent_upper
        try:
            replay_count+=1
            if restoration_mode=='controlled':
                from solar_controlled_terminal_return import controlled_terminal_cycle
                controlled=controlled_terminal_cycle(material,cc,terminal_policy)
                out=controlled['original_prefix'];score=controlled['controlled_tolerance_net_J']
                mode_candidates.append(dict(mode=restoration_mode,accepted=score is not None,
                    gross_paid_J=controlled['controlled_return']['gross_paid_J']))
            else:
                out=cycle(material,cc)
                score=out['strict_campaign_net_J'] if restoration_mode=='finite_tolerance' else None
                if restoration_mode=='asymptotic':
                    # A prefix with a conditional tail interval is NOT an
                    # admitted asymptotic restored witness.
                    mode_candidates.append(dict(mode=restoration_mode,accepted=False,tail=out['asymptotic_tail']))
            if exact_ceiling is not None:
                rational=rational_reflection_enclosure(out['sensitivity_trace'],mid,lo,hi,dt,port,edge,'terminal_load_rate_s_inv' in cfg)
                rational_candidates.append(rational)
                rational_upper=exact_ceiling-F(rational['reflection_lower_exact'])
                upper=min(upper,rational_upper)
                if restoration_mode!='asymptotic':
                    # Controlled return can change material current but leaves
                    # E/B exactly untouched. Never prune using pre-control J.
                    count=ne+nf if restoration_mode=='controlled' else ne+nf+9*len(vol)
                    field=np.asarray(out['history'][-1])[:count]
                    ex=rational_restoration_exclusion(field,out['exact_binary_field_solve_error'],
                        rational['parameter_error_exact'],cfg.get('return_atol',[1e-10]*4)[0])
                    if ex['excluded']:
                        restoration_exclusions.append(dict(lo=lo.tolist(),hi=hi.tolist(),mode=restoration_mode,**ex))
                        return
            else:
                en=reflection_enclosure(out['sensitivity_trace'],mid,lo,hi,dt,port,edge,'terminal_load_rate_s_inv' in cfg)
                upper=min(upper,ceiling-en['reflection_lower_J'])
            if center_feasible and score is not None and np.isfinite(score):best=score if best is None else max(best,score)
        except (ValueError,AssertionError,ArithmeticError,np.linalg.LinAlgError,FloatingPointError):
            failed+=1;upper=parent_upper # retain parent upper; never discard failed region
        seq+=1; heapq.heappush(queue,(-upper,seq,lo,hi))
    lo=np.zeros(ne); hi=np.zeros(ne); hi[ids]=budget
    box(lo,hi,exact_ceiling if exact_ceiling is not None else ceiling)
    for _ in range((max_boxes-1)//2):
        if not queue:break
        neg,_,lo,hi=heapq.heappop(queue)
        j=int(np.argmax(hi-lo))
        if hi[j]==lo[j]:
            seq+=1; heapq.heappush(queue,(neg,seq,lo,hi)); break
        m=lo[j]+(hi[j]-lo[j])/2
        if not lo[j]<m<hi[j]:
            seq+=1; heapq.heappush(queue,(neg,seq,lo,hi)); break
        h=hi.copy(); h[j]=m
        l=lo.copy(); l[j]=m
        box(lo,h,-neg);box(l,hi,-neg)
    no_restored_chart=bool(exact_ceiling is not None and not queue)
    upper=max((-item[0] for item in queue),default=exact_ceiling if exact_ceiling is not None else ceiling)
    if best is not None and best>upper+1e-8*max(1.,abs(upper)):
        raise ArithmeticError('candidate enclosure violated by replay')
    return dict(upper_candidate_J=float(upper),
                upper_exact_binary_chart=None if exact_ceiling is None else str(upper),
                best_center_net_J=best,
                center_replays=replay_count,failed_replays=failed,remaining_boxes=len(queue),
                gap_J=None if best is None else float(upper-best),
                rational_trace_candidates=rational_candidates,
                restoration_mode=restoration_mode,mode_candidates=mode_candidates,
                scope='conditional source-funded upper bound for matched terminal policy; no physical or outward-rounded certification',
                restoration_exclusions=restoration_exclusions,
                no_restored_passive_on_binary_chart=no_restored_chart,
                fixed_binary_nonfrozen_history=bool(cfg.get('retain_nonfrozen_event_residuals',False)),
                physical_material_rounding_enclosed=False,
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
