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
            base=campaign_jvp(material,cc,np.zeros_like(template_h),np.zeros_like(template_l))
            grads=[];rest_grads=[]
            for dh,dl in ((template_h,np.zeros_like(template_l)),
                          (np.zeros_like(template_h),template_l)):
                j=campaign_jvp(material,cc,dh,dl)
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
        except (AssertionError,ValueError,FloatingPointError,np.linalg.LinAlgError) as ex:
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
                if not e['ok'] or np.any(e['restoration_ratio']>1.):continue
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
