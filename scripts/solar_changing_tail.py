"""Changing birth-free source-off tail: operator perturbation and block certificate.

The reference uses the right support, not the discontinuous all-zero padded
generator. Real-arithmetic material bounds are numerical candidates until
rounded outward. Exact rational block proof is separate.
"""
import numpy as np
import sympy as S

def tail_envelope(model,pop,theta,vol,rows,neutral,mass,charge,alpha,cap,cool,dt,k):
    """Uniform all-j>=k distance bound to right-limit frozen split step.

    Fixed atlas, fixed terminal loads, zero forcing, no baseline ionization.
    All actual active species remain positive at finite time. Inactive slots
    may be extended by identity in the affine event (zero on physical input).
    The bound uses the sum of absolute generator-entry changes, so it
    bounds the sum of local stage operator norms, not just the full matrix norm.
    """
    pop,theta,vol,neutral,mass,charge,alpha,cap,cool=map(lambda a:np.asarray(a,float),
        (pop,theta,vol,neutral,mass,charge,alpha,cap,cool))
    n=len(vol); me=np.asarray(model['energy_masses'][0]);W=np.asarray(model['material_map'])
    if pop.shape!=(n,3) or theta.shape!=vol.shape or cap.shape!=vol.shape or cool.shape!=vol.shape or alpha.shape!=(2,) or W.shape!=(len(me),3*n):
        raise ValueError('tail chart mismatch')
    if not all(np.isfinite(a).all() for a in (pop,theta,vol,neutral,mass,charge,alpha,cap,cool,W,me)) or np.any(pop<0) or np.any(theta<0) or np.any(vol<=0) or np.any(me<=0) or np.any(alpha<=0) or np.any(cap<=0) or np.any(cool<=0) or np.any(mass<=0) or dt<=0 or k<0 or int(k)!=k:
        raise ValueError('invalid tail envelope')
    if not np.allclose(pop[:,0],pop[:,1:].sum(axis=1),rtol=1e-12,atol=0):
        raise ValueError('charge-neutral tail required')
    e=pop[:,0]; upper=e/(1+k*dt*float(alpha.min())*e)
    thermal=theta*np.exp(-k*dt*cool/cap)
    T=np.array([r['te'] for r in rows]); Tmax=T+theta
    if np.any(T<=0) or np.any(Tmax>=1/1.21e-4) or np.any(neutral[:,1:4]<0):
        raise ValueError('collision law outside admitted domain')
    O,N2,O2=neutral[:,1],neutral[:,2],neutral[:,3]
    # Absolute derivative bound for the existing 2017 collision law.
    Lips=2.33e-17*N2*np.maximum(abs(1-2*1.21e-4*T),abs(1-2*1.21e-4*Tmax))
    Lips+=1.82e-16*O2*(.5/np.sqrt(T)+.036)
    Lips+=8.9e-17*O*(.5/np.sqrt(T)+1.5*5.7e-4*np.sqrt(Tmax))
    coupling=0.
    for i in range(n):
        base=np.sum(abs(W[:,3*i:3*i+3]/np.sqrt(me*vol[i])[:,None]))
        coupling+=2*base*np.sum(np.sqrt(upper[i]/mass)*abs(charge)*(pop[i]>0))
    collision=3*np.sum(Lips*thermal*(pop[:,0]>0))
    # Each no-birth event contracts with factor sqrt(survival), approaching I.
    event=min(1.,dt*float(alpha.max())*float(np.max(upper,initial=0.))/2)
    delta=min(2.,event+dt*(coupling+collision))
    return dict(step=k,operator_step_error_upper_candidate=float(delta),
        event_error_upper_candidate=float(event),exchange_entry_sum_upper_candidate=float(coupling),
        collision_entry_sum_upper_candidate=float(collision),electron_upper_m3=upper.tolist(),
        active_right_support=(pop>0).tolist(),outward_rounding_certified=False)

def exact_uniform_block(T,K,block_steps,step_error):
    """Conditional exact rational bound on a COMMON invariant subspace.

    For every future step S_j assume ||S_j||<=1, S_j im K subset im K,
    and ||S_j-T||<=step_error (Euclidean induced norms on im K).
    Products telescope: ||S_(j+m-1)...S_j - T^m|| <= m*step_error.
    No future invariance or error premise is inferred by this routine.
    """
    T=S.Matrix(T);K=S.Matrix(K);delta=S.Rational(step_error);m=int(block_steps)
    if T.rows!=T.cols or K.rows!=T.rows or K.cols==0 or K.rank()!=K.cols or m<1 or m!=block_steps or delta<0 or not all(v.is_Rational for v in list(T)+list(K)):
        raise ValueError('invalid rational common-subspace chart')
    G=K.T*K;C=G.inv()*K.T*T*K
    if T*K!=K*C or not (G-C.T*G*C).is_positive_semidefinite:
        raise ValueError('reference subspace not invariant and contractive')
    B=(C**m).T*G*C**m
    for j in range(1,33):
        rho=1-S.Rational(1,2**j)
        if (rho*rho*G-B).is_positive_semidefinite:
            q=rho+m*delta
            return dict(status='CONDITIONAL_UNIFORM_CONTRACTION' if q<1 else 'PERTURBATION_TOO_LARGE',
                reference_rho=str(rho),block_rho_upper=str(q),block_steps=m,
                common_subspace_rank=K.cols,conditional_decay_proved=bool(q<1),
                requires_all_future_invariance=True,requires_certified_uniform_step_error=True,
                actual_changing_material_return_admitted=False)
    return dict(status='NO_REFERENCE_CONTRACTION',conditional_decay_proved=False,
        actual_changing_material_return_admitted=False)

def right_limit_reference(material,cfg,pop):
    """Actual terminal generator on the fixed support of a birth-free tail.
    Inactive padded current slots excluded from the occupied subspace.
    """
    from solar_spherical_cycle import geometry
    from solar_spherical_material_weld import construct,structural_stage_atlas
    from solar_material_generator_jvp import amplitude_material_boundary_jvp
    from solar_earth_collision_tensor import rates
    from solar_matrix_storage import diagonal
    from solar_physical_cone import timed_step
    depth=int(cfg.get('nested_depth',0));sparse=bool(depth or cfg.get('sparse_operator',False))
    if np.any(np.asarray(cfg['kinetics']['ionization_s_inv'])!=0):
        raise ValueError('birth-free tail requires zero baseline ionization')
    rows,neutral,D,gyro,axis=material
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'],depth)
    pop=np.asarray(pop,float);active=pop>0
    if pop.shape!=(len(vol),3) or np.any(pop<0):raise ValueError('invalid right support')
    nu=rates(rows,neutral);z=np.zeros_like(pop)
    model=construct(cfg['radii_m'],cfg['angular_level'],np.arange(len(vol)),vol,z,nu,gyro,axis,
        nested_depth=depth,sparse_operator=sparse)
    right=amplitude_material_boundary_jvp(model,vol,z,z,nu,z,gyro,axis,active)['right_limit']
    N=right.shape[0];port=np.zeros(N);port[int(cfg['source_edge'])]=float(cfg['source_coupling_sqrt_inv_s'])
    load=np.asarray(cfg.get('terminal_load_rate_s_inv',cfg['load_rate_s_inv']),float)
    if load.shape!=(ne,) or np.any(load<0):raise ValueError('invalid terminal receiver')
    H=right-diagonal(np.r_[load,np.zeros(N-ne)]+port**2,sparse)
    atlas=structural_stage_atlas(model,mesh)
    occupied=np.r_[np.ones(ne+nf,dtype=bool),np.repeat(active.ravel(),3)]
    dt=float(cfg['period_s'])/len(cfg['incident_sqrt_W'])
    # All future stages leave this coordinate subspace invariant: no birth,
    # inactive species have zero coupling/local block, and the affine event
    # is diagonal. This statement needs support to remain mathematically
    # positive, not numerically underflowed.
    _,receipt=timed_step(np.zeros(N),H,np.zeros(N),dt,mesh,atlas_pairs=atlas)
    return dict(generator=H,receipt=receipt,occupied=occupied,atlas=atlas,dt=dt,model=model,
        finite_reaction_support_premise=True,physical_admission=False)

def reverse_tail_start(envelope,target,max_steps=2**40):
    """Back-solve smallest integer step satisfying monotone numerical envelope.
    The callback must be the actual monotone tail_envelope, not a sample fit.
    """
    if not 0<target<1 or max_steps<1:raise ValueError('invalid contraction margin')
    def ok(k):return envelope(k)['operator_step_error_upper_candidate']<=target
    if ok(0):return dict(status='CANDIDATE',start_step=0,outward_rounding_certified=False)
    hi=1
    while hi<max_steps and not ok(hi):hi=min(hi*2,max_steps)
    if not ok(hi):return dict(status='MARGIN_NOT_REACHED',outward_rounding_certified=False)
    lo=0
    while hi-lo>1:
        m=(lo+hi)//2
        if ok(m):hi=m
        else:lo=m
    return dict(status='CANDIDATE',start_step=hi,operator_step_error_upper_candidate=envelope(hi)['operator_step_error_upper_candidate'],
        outward_rounding_certified=False)
