"""Bounded joint activation/receiver search on the same spherical cycle.
Search results are feasible numerical candidates, not global certificates.
All candidates share the same incident history, clock, material and mesh.
"""
import numpy as np
from scipy.optimize import differential_evolution
from solar_spherical_cycle import cycle,four_worlds,geometry

def optimize(material,cfg,design):
    """Finite geometry family: explicitly enumerated source/receiver layouts.
    Receiver allocation and heating are bounded by shared resource budgets.
    A geometry layout is a support mask on actual edge IDs, not a ratio label.
    """
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'])
    cfg=dict(cfg,fixed_horizon=True)
    if 'layout_geometry' in design:
        from solar_spherical_layouts import layouts as generate
        layouts=generate(cfg['radii_m'],cfg['angular_level'],**design['layout_geometry'])
    else: layouts=design['layouts']
    n=len(vol); steps=len(cfg['incident_sqrt_W'])
    budget=float(design['load_budget_s_inv']); heater=float(design['heating_budget_J'])
    dt=cfg['period_s']/steps
    assert budget>0 and heater>=0 and len(layouts)>0
    # Identical resource ceiling also applies to terminal receiver loading.
    if 'terminal_load_rate_s_inv' in cfg:
        terminal=np.asarray(cfg['terminal_load_rate_s_inv'],float)
        assert terminal.shape==(ne,) and np.all(terminal>=0) and terminal.sum()<=budget
    eligible=set(e for layout in layouts for e in layout['receiver_edges'])
    if 'terminal_load_rate_s_inv' in cfg:
        assert set(np.flatnonzero(terminal))<=eligible
    # Each candidate specifies a finite set of eligible receiver edge IDs.
    results={}; evaluations=0
    def run(layout,active):
        nonlocal evaluations
        ids=np.asarray(layout['receiver_edges'],int)
        if not len(ids): return dict(status='UNRESOLVED_MESH_LAYOUT',rejected=0)
        assert len(set(ids))==len(ids) and np.all((ids>=0)&(ids<ne))
        heat_cells=np.asarray(design['heater_cells'],int)
        assert len(set(heat_cells))==len(heat_cells) and np.all((heat_cells>=0)&(heat_cells<n))
        count=len(ids); hc=steps*len(heat_cells) if active else 0
        best=None; rejected=0
        def decode(z):
            cc=dict(cfg)
            allocation=np.zeros(ne); raw=np.asarray(z[:count])
            allocation[ids]=budget*raw/max(1.,raw.sum())
            heat=np.zeros((steps,n))
            if hc:
                raw=np.asarray(z[count:]); heat[:,heat_cells]=(heater/(dt*cfg['max_cycles'])*raw/max(1.,raw.sum())).reshape(steps,-1)
            cc['load_rate_s_inv']=allocation
            cc['heating_W']=heat
            return cc
        def objective(z):
            nonlocal best,rejected,evaluations
            evaluations+=1; cc=decode(z)
            try: out=cycle(material,cc)
            except (ValueError,AssertionError,np.linalg.LinAlgError,FloatingPointError):
                rejected+=1; return 1e100
            # Only strict campaign return is admitted for endpoint objective.
            score=out['strict_campaign_net_J']
            if score is None or not np.isfinite(score):
                rejected+=1; return 1e100
            if best is None or score>best[0]: best=(score,np.array(z),out)
            return -score
        zeros=np.zeros(count+hc); objective(zeros)
        differential_evolution(objective,[(0.,1.)]*(count+hc),
            seed=int(design.get('seed',369)),maxiter=int(design.get('maxiter',4)),
            popsize=int(design.get('popsize',4)),polish=False,workers=1)
        if best is None:return dict(status='NO_ADMITTED_WITNESS',rejected=rejected)
        score,z,out=best; cc=decode(z)
        return dict(status='CANDIDATE',net_J=score,load=cc['load_rate_s_inv'].tolist(),
                    heating=cc['heating_W'].tolist(),campaign=out,rejected=rejected)
    for layout in layouts:
        label=layout['id']; assert label not in results
        results[label]={k:run(layout,a) for k,a in [('passive',False),('active',True)]}
    def select(k):
        valid=[(v[k]['net_J'],label,v[k]) for label,v in results.items() if v[k]['status']=='CANDIDATE']
        return max(valid,key=lambda p:p[0]) if valid else None
    a,p=select('active'),select('passive')
    # Energy ceiling for the same fixed campaign length. Natural source on
    # during preparation is not free headroom: include it in the campaign.
    ceiling=cfg['max_cycles']*dt*float(np.sum(np.asarray(cfg['incident_sqrt_W'])**2))
    # Uniform bound for source-edge scattering: when source edge is eligible,
    # load at that site is <= budget. This does not bound remote receiver
    # extraction by itself. Use only the universal incident cap unless a
    # separately checked full-state domination certificate is supplied.
    result=dict(layouts=results,layout_geometry=layouts,evaluations=evaluations,universal_passive_upper_J=ceiling,
        best_active=None if a is None else a[0],best_passive=None if p is None else p[0],
        sampled_advantage_J=None if a is None or p is None else a[0]-p[0],
        candidate_advantage_lower_J=None if a is None else a[0]-ceiling,
        global_optimum_certified=False,physical_admission=False)
    if a:
        cc=dict(cfg,load_rate_s_inv=a[2]['load'],heating_W=a[2]['heating'])
        result['active_four_worlds']=four_worlds(material,cc)
    return result

def reverse_target(material,cfg,design,target_J):
    """Return witnessed target residual and honest upper ceiling gap."""
    out=optimize(material,cfg,design)
    a=out['best_active']; p=out['best_passive']; upper=out['universal_passive_upper_J']
    out.update(target_J=float(target_J),sampled_target_residual_J=None if a is None or p is None else a-p-target_J,
        candidate_target_residual_J=None if a is None else a-upper-target_J)
    return out
