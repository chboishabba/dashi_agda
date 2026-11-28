"""Two-control, original-state constrained spherical inverse search.

Finite smooth positive-population chart; each optimization result is replayed
through the original cycle. Numerical candidates are not global optima.
The source, material, geometry, horizon and resource budgets are shared.
"""
import numpy as np
from scipy.optimize import minimize
from solar_spherical_cycle import cycle,geometry,four_worlds
from solar_spherical_reverse_jvp import campaign_jvp
from solar_physical_causal import MASS,CHARGE

def reverse_constrained(material,cfg,design):
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'])
    n=len(vol);src=np.asarray(cfg['incident_sqrt_W'],float)
    template_h=np.asarray(design['heater_pattern_W'],float)
    template_l=np.asarray(design['load_pattern_s_inv'],float)
    assert template_h.shape==(len(src),n) and template_l.shape==(ne,)
    assert np.all(template_h>=0) and np.all(template_l>=0)
    assert np.sum(template_l)<=design['load_budget_s_inv']+1e-14
    dt=float(cfg['period_s'])/len(src)
    assert cfg['max_cycles']*dt*np.sum(template_h)<=design['heating_budget_J']+1e-14
    assert int(cfg['max_cycles'])>=1 and cfg.get('fixed_horizon',True)
    assert cfg.get('return_rtol',0)>=0
    if 'terminal_load_rate_s_inv' in cfg:
        terminal=np.asarray(cfg['terminal_load_rate_s_inv'],float)
        assert terminal.shape==(ne,) and np.all(terminal>=0)
        assert terminal.sum()<=design['load_budget_s_inv']+1e-14
    original=(np.zeros(ne+nf+9*n),
              np.asarray(material[2],float)*MASS/CHARGE**2,
              np.asarray(cfg['kinetics']['initial_neutral_m3'],float),
              np.zeros(n))
    tol=np.asarray(cfg.get('return_atol',[1e-10]*4),float)
    allowances=[float(tol[i]+cfg['return_rtol']*np.linalg.norm(v)) for i,v in enumerate(original)]
    assert all(a>0 for a in allowances)
    memo={}
    calls=0
    def evaluate(z):
        nonlocal calls
        key=tuple(float(v) for v in z)
        if key in memo:return memo[key]
        calls+=1; cc=dict(cfg,fixed_horizon=True,
            heating_W=(z[0]*template_h).tolist(),
            load_rate_s_inv=(z[1]*template_l).tolist(),
            retain_sensitivity=False,retain_history=False)
        try:
            # Both directional runs contain the identical primal trajectory.
            # Reuse the first instead of recomputing a third zero-JVP campaign.
            heater_j=campaign_jvp(material,cc,template_h,np.zeros_like(template_l))
            load_j=campaign_jvp(material,cc,np.zeros_like(template_h),template_l)
            base=heater_j
            grads=[];rest_grads=[]
            for j in (heater_j,load_j):
                if not np.isclose(j['campaign_net_J'],base['campaign_net_J'],
                                  rtol=1e-11,atol=1e-12):
                    raise ArithmeticError('primal mismatch between JVP directions')
                grads.append(j['dcampaign_net_J'])
                rest_grads.append([2*float(np.sum((v-u)*dv))
                    for v,u,dv in zip(base['endpoint'],original,j['endpoint_jvp'])])
            # Smooth squared original-state return contract. The norm's
            # gradient is undefined at exact restoration and must not be
            # silently replaced by zero using an arbitrary denominator.
            res=np.array([float(np.sum((v-u)**2))/allowances[i]**2
                for i,(v,u) in enumerate(zip(base['endpoint'],original))])
            jac=np.array(rest_grads,dtype=float).T/np.asarray(allowances)[:,None]**2
            out=dict(ok=True,net=float(base['campaign_net_J']),
                gradient=np.asarray(grads,float),restoration_squared_ratio=res,
                restoration_squared_jacobian=jac,config=cc)
        except (AssertionError,ValueError,ArithmeticError,FloatingPointError,np.linalg.LinAlgError) as ex:
            out=dict(ok=False,error=type(ex).__name__+': '+str(ex))
        memo[key]=out
        return out
    def solve(active):
        bounds=[(0.,1.) if active else (0.,0.),(0.,1.)]
        def value(z):
            e=evaluate(z)
            return -e['net'] if e['ok'] else 1e30
        def gradient(z):
            e=evaluate(z)
            return -e['gradient'] if e['ok'] else np.zeros(2)
        cons=[dict(type='ineq',
                   fun=lambda z,i=i: 1.-evaluate(z)['restoration_squared_ratio'][i]
                        if evaluate(z)['ok'] else -1e15,
                   jac=lambda z,i=i: -evaluate(z)['restoration_squared_jacobian'][i]
                        if evaluate(z)['ok'] else np.zeros(2)) for i in range(4)]
        candidates=[]
        for seed in ((0.,0.),(0.,1.),(1.,0.),(1.,1.)):
            if not active and seed[0]:continue
            opt=minimize(value,np.asarray(seed,float),jac=gradient,method='SLSQP',
                bounds=bounds,constraints=cons,
                options=dict(maxiter=int(design.get('maxiter',30)),ftol=1e-9))
            for z in (opt.x,np.asarray(seed,float)):
                e=evaluate(z)
                if not e['ok'] or np.any(e['restoration_squared_ratio']>1.):continue
                original_replay=cycle(material,e['config'])
                if original_replay['strict_campaign_net_J'] is None:continue
                candidates.append((float(original_replay['strict_campaign_net_J']),
                    z.tolist(),original_replay))
        if not candidates:return dict(status='NO_RESTORED_WITNESS')
        score,z,replay=max(candidates,key=lambda t:t[0])
        return dict(status='SAMPLED_RESTORED_CANDIDATE',
            strict_net_J=score,control=z,original_replay=replay)
    passive=solve(False);active=solve(True)
    gap=None
    if all(x['status']=='SAMPLED_RESTORED_CANDIDATE' for x in (active,passive)):
        gap=active['strict_net_J']-passive['strict_net_J']
    selected_four_worlds=None
    if active['status']=='SAMPLED_RESTORED_CANDIDATE':
        z=active['control']
        cc=dict(cfg,fixed_horizon=True,
            heating_W=(z[0]*template_h).tolist(),
            load_rate_s_inv=(z[1]*template_l).tolist())
        selected_four_worlds=four_worlds(material,cc)
    return dict(active=active,passive=passive,
                active_selected_four_worlds=selected_four_worlds,
                sampled_advantage_J=gap,derivative_evaluations=calls,
                strongest_passive_certified=False,global_optimum_certified=False,
                physical_admission=False)

def quadratic_ray_seeds(net,returns,smax,target=0.):
    """Bidi solve of the coefficient polynomial; candidates only, no remainder bound.
    net and each normalized return polynomial use ascending coefficients.
    """
    if not np.isfinite(smax) or smax<=0: raise ValueError('positive finite ray interval required')
    net=np.asarray(net,float); returns=np.asarray(returns,float)
    if net.shape!=(3,) or returns.shape!=(4,3) or not np.isfinite(net).all() or not np.isfinite(returns).all():
        raise ValueError('invalid quadratic residual fibre')
    cuts={0.,float(smax)}
    def roots(c):
        for z in np.polynomial.polynomial.polyroots(c):
            if abs(z.imag)<=1e-10 and 0<=z.real<=smax: cuts.add(float(z.real))
    for row in returns: roots(row-np.array([1.,0.,0.]))
    roots(net-np.array([target,0.,0.]))
    if net[2]!=0:
        z=-net[1]/(2*net[2])
        if 0<z<smax: cuts.add(float(z))
    points=sorted(cuts)
    probes=sorted(set(points+[(a+b)/2 for a,b in zip(points,points[1:])]))
    def score(s): return float(np.polynomial.polynomial.polyval(s,net))
    def residual(s): return np.array([np.polynomial.polynomial.polyval(s,row) for row in returns])
    return sorted([dict(s=s,predicted_net_J=score(s),predicted_return=residual(s).tolist(),
        predicted_target_residual_J=score(s)-target) for s in probes],
        key=lambda z:(max(z['predicted_return'])<=1.,z['predicted_net_J']),reverse=True)

def reverse_quadratic_ray(material,cfg,dheating,dload,design,target_J=0.,smax=1.):
    """Use native signed jet to propose control rays and replay actual campaign.
    Same budget throughout. Taylor feasibility is never terminal feasibility.
    """
    cc=dict(cfg,common_stage_atlas=True,fixed_horizon=True)
    h=np.asarray(cc['heating_W'],float); l=np.asarray(cc['load_rate_s_inv'],float)
    dh=np.asarray(dheating,float); dl=np.asarray(dload,float)
    dt=cc['period_s']/len(cc['incident_sqrt_W'])
    if h.shape!=dh.shape or l.shape!=dl.shape: raise ValueError('ray shape mismatch')
    for s in (0.,smax):
        H=h+s*s*dh; L=l+s*s*dl
        if np.any(H<0) or np.any(L<0) or dt*cc['max_cycles']*H.sum()>design['heating_budget_J'] or L.sum()>design['load_budget_s_inv']:
            raise ValueError('ray outside shared resources')
    if 'terminal_load_rate_s_inv' in cc:
        term=np.asarray(cc['terminal_load_rate_s_inv'],float)
        if term.shape!=l.shape or np.any(term<0) or term.sum()>design['load_budget_s_inv']:
            raise ValueError('terminal load outside shared resources')
    j=campaign_jvp(material,cc,dh,dl,quadratic_amplitude_path=True,quadratic_second_order=True)
    end=j['endpoint']; first=j['endpoint_jvp']; second=j['endpoint_coefficient2']
    original=(np.zeros_like(end[0]),np.asarray(material[2])*MASS/CHARGE**2,
        np.asarray(cc['kinetics']['initial_neutral_m3']),np.zeros_like(end[3]))
    tol=np.asarray(cc.get('return_atol',[1e-10]*4))+cc['return_rtol']*np.array([np.linalg.norm(z) for z in original])
    if np.any(tol<=0): raise ValueError('positive return tolerances required')
    returns=np.array([[np.sum((x-o)**2),2*np.sum((x-o)*a),
        np.sum(a*a)+2*np.sum((x-o)*b)] for x,o,a,b in zip(end,original,first,second)])/tol[:,None]**2
    net=[j['campaign_net_J'],j['dcampaign_net_J'],j['net_coefficient2_J']]
    seeds=quadratic_ray_seeds(net,returns,smax,target_J)
    # Probe backtracking points as well: the quadratic model is not certified.
    proposals=sorted(set([0.,float(smax)]+[q['s'] for q in seeds]+[q['s']/2 for q in seeds]))
    trials=[]; best=None
    for s in proposals:
        trial=dict(cc,heating_W=(h+s*s*dh).tolist(),load_rate_s_inv=(l+s*s*dl).tolist())
        try:
            out=cycle(material,trial)
            score=out['strict_campaign_net_J']
            trials.append(dict(s=s,strict_net_J=score,return_residual=out['original_return']))
            if score is not None and (best is None or score>best[0]): best=(score,s,trial)
        except (ValueError,AssertionError,ArithmeticError,np.linalg.LinAlgError,FloatingPointError) as exc:
            trials.append(dict(s=s,rejected=str(exc)))
    return dict(net_coefficients=net,return_coefficients=returns.tolist(),predicted_seeds=seeds,
        trials=trials,restored_witness=None if best is None else dict(net_J=best[0],s=best[1],
            target_residual_J=best[0]-target_J,four_worlds=four_worlds(material,best[2])),
        Taylor_remainder_certified=False,global_optimum_certified=False,physical_admission=False)
