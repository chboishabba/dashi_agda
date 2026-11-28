"""Source-off tail bounds on the ORIGINAL spherical reaction/thermal law.

No new control, reset, or change in rate coefficients. Analytic inequalities
are exact real-arithmetic statements; float evaluations are candidates.
"""
import numpy as np

def recombination_tail_geometry(pop,initial,pool,initial_pool,alpha,dt,steps):
    """For zero ionization and no heater, n_e(k)<=1/(1/n_e(0)+k*h*alpha_min).
    Strictly positive alpha for both channels. Charge and ion+neutral
    inventory remain invariant. Only an initially zero population can
    generally return under this tail; an initially positive target cannot.
    """
    pop,initial,pool,initial_pool,alpha=map(lambda x:np.asarray(x,float),(pop,initial,pool,initial_pool,alpha))
    if pop.ndim!=2 or pop.shape[1]!=3 or initial.shape!=pop.shape or pool.shape!=initial_pool.shape or pool.shape!=(len(pop),2) or alpha.shape!=(2,):
        raise ValueError('tail geometry shape mismatch')
    if not all(np.isfinite(x).all() and np.all(x>=0) for x in (pop,initial,pool,initial_pool,alpha)):
        raise ValueError('nonfinite or negative tail data')
    if np.any(alpha<=0) or not np.isfinite(dt) or dt<=0 or int(steps)!=steps or steps<0:
        raise ValueError('strictly positive recombination and finite nonnegative clock required')
    if not all(np.allclose(x[:,0],x[:,1:].sum(axis=1),rtol=1e-12,atol=0) for x in (pop,initial)):
        raise ValueError('charge-neutral tail required')
    if not np.allclose(pop[:,1:]+pool,initial[:,1:]+initial_pool,rtol=1e-12,atol=0):
        raise ValueError('original ion-neutral inventory mismatch')
    e=pop[:,0]; bound=np.divide(e,1+steps*dt*float(alpha.min())*e)
    # ||(n_e,n_1,n_2)|| <= sqrt(2)*n_e; neutral residual norm <= n_e.
    target_zero=not bool(np.any(initial))
    return dict(steps=int(steps),electron_upper_m3=bound.tolist(),
        population_norm_upper=float(np.sqrt(2)*np.linalg.norm(bound)) if target_zero else None,
        pool_norm_upper=float(np.linalg.norm(bound)) if target_zero else None,
        asymptotic_population_return=target_zero,
        asymptotic_pool_return=target_zero,
        finite_positive_population_exact_return_obstructed=bool(target_zero and np.any(e>0)),
        nonzero_initial_population_limit_obstructed=not target_zero,
        outward_rounding_certified=False)

def remaining_tail_work(field,pop,vol,formation,recovery_efficiency):
    """Source-off, birth-free, no additional auxiliary tariff:
    future useful work <= present normalized field/current storage.
    Future chemical recovery <= recoverable present formation store.
    Neither thermal storage nor absent external source is credited as useful.
    """
    x,p,V,c=map(lambda v:np.asarray(v,float),(field,pop,vol,formation))
    if p.ndim!=2 or p.shape[1]!=3 or V.shape!=(len(p),) or c.shape!=(3,):
        raise ValueError('tail work shape mismatch')
    if not all(np.isfinite(v).all() for v in (x,p,V,c)) or np.any(p<0) or np.any(V<=0) or np.any(c<0) or not 0<=recovery_efficiency<=1:
        raise ValueError('invalid tail work input')
    field_J=float(x@x/2); formation_J=float(np.einsum('is,i,s->',p,V,c))
    recovered_J=recovery_efficiency*formation_J
    return dict(field_storage_J=field_J,formation_storage_J=formation_J,
        additional_useful_upper_J=field_J,additional_recovery_upper_J=recovered_J,
        additional_net_lower_J=0.,additional_net_upper_J=field_J+recovered_J,
        requires_no_extra_tail_tariff=True,field_return_admitted=False,
        outward_rounding_certified=False)

def source_off_tail_receipt(field,pop,pool,theta,initial_pop,initial_pool,vol,chem,cap,cool,kinetics,dt,steps):
    """Bound continuing the same source-off terminal policy, not a reset."""
    if np.any(np.asarray(kinetics['ionization_s_inv'])!=0):
        return dict(status='BASELINE_IONIZATION_PREVENTS_BIRTH_FREE_TAIL',physical_admission=False)
    alpha=np.asarray(kinetics['recombination_m3_s'],float)
    if np.any(alpha<=0):
        return dict(status='STRICT_RECOMBINATION_RATE_MISSING',physical_admission=False)
    p=recombination_tail_geometry(pop,initial_pop,pool,initial_pool,alpha,dt,steps)
    w=remaining_tail_work(field,pop,vol,chem,kinetics['chemical_recovery_efficiency'])
    th=np.asarray(theta,float); cap=np.asarray(cap,float);cool=np.asarray(cool,float)
    if th.shape!=cap.shape or cap.shape!=cool.shape or np.any(th<0) or np.any(cap<=0) or np.any(cool<=0):
        raise ValueError('invalid thermal tail chart')
    thermal=float(np.linalg.norm(th*np.exp(-steps*dt*cool/cap)))
    return dict(status='CONDITIONAL_SOURCE_OFF_TAIL_ENCLOSURE',population=p,work=w,
        thermal_norm_candidate=thermal,asymptotic_thermal_return=True,
        field_return_admitted=False,asymptotic_full_return_admitted=False,
        physical_admission=False)
