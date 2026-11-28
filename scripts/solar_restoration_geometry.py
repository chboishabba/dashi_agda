"""Original positive thermal/reaction return geometry.
The log-domain numerical evaluation is not outward-rounded certification.
Analytic finite-return obstructions follow from strictly positive survival.
"""
import numpy as np
from scipy.special import logsumexp

def thermal_return_geometry(heat,dt,capacity,cooling,horizon,tail,atol):
    heat=np.asarray(heat,float); cap=np.asarray(capacity,float); cool=np.asarray(cooling,float)
    if heat.ndim!=2 or cap.shape!=(heat.shape[1],) or cool.shape!=cap.shape:
        raise ValueError('thermal shape mismatch')
    if not all(np.isfinite(v).all() for v in (heat,cap,cool)) or not np.isfinite(dt) or dt<=0:
        raise ValueError('nonfinite thermal input')
    if np.any(heat<0) or np.any(cap<=0) or np.any(cool<=0) or horizon<1 or tail<0 or not np.isfinite(atol) or atol<0:
        raise ValueError('invalid positive thermal path')
    if int(horizon)!=horizon or int(tail)!=tail: raise ValueError('integer clock required')
    lam=dt*cool/cap
    if np.any(lam<=0) or not np.isfinite(lam).all(): raise ValueError('thermal decay underflow/overflow')
    logbeta=np.log(-np.expm1(-lam))-np.log(cool)
    steps=np.tile(heat,(int(horizon),1))
    logheat=np.full_like(steps,-np.inf); positive=steps>0
    logheat[positive]=np.log(steps[positive])
    delay=np.arange(len(steps)-1,-1,-1)[:,None]
    logpre=logsumexp(logheat+logbeta-delay*lam,axis=0)
    logfinal=logpre-tail*lam
    lognorm=float(logsumexp(2*logfinal)/2)
    active=bool(np.any(positive))
    if not active:
        necessary=sufficient=0; predicted=True
    elif atol==0:
        necessary=sufficient=None;predicted=False
    else:
        target=np.log(atol)
        necessary=max(0,int(np.ceil(np.max((logpre-target)/lam))))
        # ||diag(exp(-lambda k))*theta|| <= exp(-min(lambda)*k)||theta||.
        pre_norm=float(logsumexp(2*logpre)/2)
        sufficient=max(0,int(np.ceil((pre_norm-target)/np.min(lam))))
        predicted=bool(lognorm<=target)
    return dict(exact_zero_return_obstructed=active,
        finite_exact_tail_exists=not active,
        log_terminal_norm=None if not np.isfinite(lognorm) else lognorm,
        tolerance_return_candidate=predicted,
        necessary_tail_steps_candidate=necessary,sufficient_tail_steps_candidate=sufficient,
        tail_steps=int(tail),outward_rounding_certified=False)

def analytic_support_return_obstruction(initial_support,birth_support):
    """For finite exponential survival with nonnegative rates, support can
    only grow. Numeric underflow or explicit removal events are separate.
    """
    initial=np.asarray(initial_support,bool); born=np.asarray(birth_support,bool)
    if initial.shape!=born.shape: raise ValueError('support shape mismatch')
    obstruction=born&~initial
    return dict(exact_zero_population_return_obstructed=bool(np.any(obstruction)),
                obstructed_indices=np.argwhere(obstruction).tolist())
