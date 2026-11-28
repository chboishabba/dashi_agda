"""Quadratic population-path lift of the original event; s>=0, u=s*s.
Density coefficients are d/du, normalized-current tangents are d/ds.
Higher-order right support is supplied by the reaction path, not inferred
from a zero first jet. Finite-velocity paths only.
"""
import numpy as np
from solar_physical_causal import event,MASS,CHARGE


def right_reaction_support(pop_support,pool_support,power,power_u,q):
    """Exact analytic support for finite exponential rates, u>=0."""
    p=np.asarray(pop_support,bool); pool=np.asarray(pool_support,bool)
    alpha=np.asarray(q['recombination_m3_s']); k=np.asarray(q['ionization_s_inv'])
    g=np.asarray(q['heater_ionization_per_J'])
    if min(power, float(np.min(alpha)),float(np.min(k)),float(np.min(g)))<0 or (power==0 and power_u<0):
        raise ValueError('invalid right reaction path')
    available=pool | (p[1:] & p[0] & (alpha>0))
    born=available & ((k>0)|((g>0)&((power>0)|(power_u>0))))
    return p | np.r_[born.any(),born],available


def event_amplitude_jvp(z,n,r,a,b,V,dz,n_u,r_u,a_u,old_right,new_right):
    """Differentiate z(s) after original event, on n(s)=n+u*n_u+o(u).
    Requires bounded old velocities; absent slots with zero amplitude slope
    have zero current slope. Birth velocities are held fixed.
    """
    z,dz,b=[np.asarray(v,float).reshape(3,3) for v in (z,dz,b)]
    n,r,a,n_u,r_u,a_u=map(lambda v:np.asarray(v,float),(n,r,a,n_u,r_u,a_u))
    old_right,new_right=map(lambda v:np.asarray(v,bool),(old_right,new_right))
    if any(v.shape!=(3,) for v in (n,r,a,n_u,r_u,a_u,old_right,new_right)) or V<=0:
        raise ValueError('invalid event chart shape')
    if not all(np.isfinite(v).all() for v in (z,dz,b,n,r,a,n_u,r_u,a_u)):
        raise ValueError('nonfinite event chart')
    remain=n-r; new=remain+a; remain_u=n_u-r_u; new_u=remain_u+a_u
    for p,pu in ((n,n_u),(r,r_u),(a,a_u),(remain,remain_u),(new,new_u)):
        if np.any(p<0) or np.any((p==0)&(pu<0)):
            raise ValueError('negative right population coefficient')
    for p,pu,support in ((n,n_u,old_right),(new,new_u,new_right)):
        if np.any(((p>0)|(pu>0))&~support):
            raise ValueError('right support contradicts density jet')
    if np.any(dz[(n==0)&(n_u==0)]!=0):
        raise ValueError('current slope without amplitude slope')
    if abs((a_u-r_u)@np.sign(CHARGE))>1e-12*max(1e-300,float(np.sum(abs(a_u)+abs(r_u)))):
        raise ValueError('directional charge mismatch')
    primal=event(z,n,r,a,b,V)
    w=V*MASS; signed=np.sign(CHARGE)*np.sqrt(w)
    dout=np.zeros_like(z); dkin=np.zeros(3)
    for j in range(3):
        if new[j]>0:
            if n[j]>0:
                dout[j]=remain[j]/np.sqrt(n[j]*new[j])*dz[j]
        elif new_u[j]>0:
            den=np.sqrt(new_u[j]); momentum=signed[j]*a_u[j]*b[j]
            if n[j]>0:
                momentum+=remain_u[j]*z[j]/np.sqrt(n[j])
            elif n_u[j]>0:
                momentum+=remain_u[j]*dz[j]/np.sqrt(n_u[j])
            dout[j]=momentum/den
        if n[j]>0:
            v=z[j]/(signed[j]*np.sqrt(n[j])); dv=dz[j]/(signed[j]*np.sqrt(n[j]))
            dkin[1]+=w[j]*r[j]*(v@dv)
            if new[j]>0:
                dkin[2]+=w[j]*remain[j]*a[j]/new[j]*((v-b[j])@dv)
    out=primal[0].reshape(3,3)
    terms=np.array([np.sum(out*dout),-np.sum(z*dz),-dkin[0],dkin[1],dkin[2]])
    if abs(terms.sum())>1e-10*max(1e-300,np.sum(abs(terms))):
        raise ArithmeticError('directional kinetic ledger mismatch')
    q=np.sqrt(n); qp=np.sqrt(new)
    dq=np.sqrt(np.where(n==0,n_u,0.)); dqp=np.sqrt(np.where(new==0,new_u,0.))
    return primal,dict(state_jvp=dout.ravel(),population_u=new_u,amplitude_jvp=dqp,
        old_right=old_right,new_right=new_right,kinetic_jvp=dkin,
        signed_amplitude_residual=qp-q,signed_tangent_residual=dqp-dq,
        density_jvp=np.zeros(3),finite_velocity_path_required=True)
