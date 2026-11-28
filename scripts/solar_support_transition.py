"""Explicit stratified species support transition on original population event.

Do not interpolate the native generator across an inactive/active species:
its gyro and collision blocks switch support. This constructor is a finite
state event with its own original energy ledger, not a zero-density JVP.
"""
import numpy as np
from solar_population_event import event, MASS, CHARGE


def support_transition(z, population, removed, created, birth, volume):
    n=np.asarray(population,float)
    r=np.asarray(removed,float); c=np.asarray(created,float)
    b=np.asarray(birth,float); current=np.asarray(z,float).reshape(3,3)
    if n.shape!=r.shape or n.shape!=c.shape or n.shape!=(3,) or b.shape!=(3,3):
        raise ValueError('support transition shape mismatch')
    if volume<=0 or not np.isfinite(volume):
        raise ValueError('nonpositive cell volume')
    if not (np.all(np.isfinite(n)) and np.all(np.isfinite(r))
            and np.all(np.isfinite(c)) and np.all(np.isfinite(current))
            and np.all(np.isfinite(b))):
        raise ValueError('nonfinite support event')
    if np.any((n==0)[:,None]&(current!=0)):
        raise ValueError('uninhabited species carries current')
    before=(n>0)
    out,new,ledger=event(current,n,r,c,b,volume)
    after=(new>0)
    znew=np.asarray(out,float).reshape(3,3)
    if np.any(znew[~after]!=0):
        raise ValueError('extinct species retains current')
    # Both maps are exact on padded support: zero slots are truly uninhabited.
    incoming,removed_energy,mixing=map(float,ledger)
    before_kinetic=float(np.sum(current**2)/2)
    after_kinetic=float(np.sum(znew**2)/2)
    residual=after_kinetic-before_kinetic-incoming+removed_energy+mixing
    tol=1e-10*max(before_kinetic,after_kinetic,incoming,removed_energy,mixing,1e-30)
    if abs(residual)>tol:
        raise ArithmeticError('support jump violates original kinetic budget')
    born=np.flatnonzero(~before&after).tolist()
    extinct=np.flatnonzero(before&~after).tolist()
    receipt=dict(before_support=before.tolist(),after_support=after.tolist(),
                 born_species=born,extinct_species=extinct,
                 support_changed=bool(born or extinct),
                 kinetic_before_J=before_kinetic,kinetic_after_J=after_kinetic,
                 incoming_birth_J=incoming,removed_kinetic_J=removed_energy,
                 mixing_J=mixing,kinetic_balance_J=residual,
                 full_generator_jvp_admitted=not bool(born or extinct),
                 original_event=True,physical_admission=False)
    return out,new,ledger,receipt
