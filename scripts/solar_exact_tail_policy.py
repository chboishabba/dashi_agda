"""Birth-free changing-tail weld on fixed binary geometry coefficients.
No convergence to a separately rounded collision matrix is required.
Input population/temperature upper bounds are premises, not validated prefix data.
"""
from fractions import Fraction as F
import numpy as np
from solar_event_rounding import q,sqrt_interval
from solar_tail_dyadic import ceil_div,preconditioned_block_certificate
from solar_population_event import MASS,CHARGE


def rate_bounds(row,neutral,theta_upper):
    """Exact rational inequalities for original 2017 collision formula.
    Constants here are the exact binary constants of the original source.
    """
    T=q(row['te']); U=T+q(theta_upper);tr=(q(row['ti'])+q(neutral[10]))/2
    O,N2,O2=map(q,neutral[1:4]);a=q(1.21e-4)
    if min(O,N2,O2)<0 or not 0<T<=U<1/a or tr<=0:raise ValueError('collision domain')
    tl,tu=sqrt_interval(T)[0],sqrt_interval(U)[1]
    low=q(2.33e-17)*N2*(1-a*U)*T+q(1.82e-16)*O2*(1+q(.036)*tl)*tl+q(8.9e-17)*O*(1+q(5.7e-4)*T)*tl
    high=q(2.33e-17)*N2*U+q(1.82e-16)*O2*(1+q(.036)*tu)*tu+q(8.9e-17)*O*(1+q(5.7e-4)*U)*tu
    vm=q(1e-16)*(q(4.29)*N2+q(4.23)*O2+q(2.41)*O)
    # The quadratic in log10(tr) has a globally positive minimum.
    c,b,a2=map(q,(1.08,.139,.00451));poly_min=c-b*b/(4*a2)
    if poly_min<=0:raise ArithmeticError('ion collision polynomial minimum')
    B=0
    while not F(1,10**B)<=tr<=10**B:B+=1
    rl,ru=sqrt_interval(tr);const=q(6.82e-16)*N2+q(6.66e-16)*O2
    vo_lo=const+q(3.42e-17)*O*rl*poly_min
    vo_hi=const+q(3.42e-17)*O*ru*(c+b*B+a2*B*B)
    return (low,vm,vo_lo),(high,vm,vo_hi)


def uniform_current_margin(rows,neutral,theta_upper,gyro,axis,active,dt):
    """Squared-norm loss for all future decoupled active current stages."""
    h=q(dt);active=np.asarray(active,bool);n=len(rows);margin=F(1)
    if h<=0 or active.shape!=(n,3) or len(theta_upper)!=n or np.shape(gyro)!=(n,3) or np.shape(axis)!=(n,3):raise ValueError('current chart')
    for i,row in enumerate(rows):
        if not active[i].any():continue
        lo,hi=rate_bounds(row,neutral[i],theta_upper[i]);idx=np.flatnonzero(active[i]);nu=min(lo[j] for j in idx)
        if nu<=0:raise ValueError('strict future collision damping missing')
        cross_sum=2*sum((abs(q(v)) for v in axis[i]),F(0))
        norm=sum((3*hi[j]+abs(q(gyro[i,j]))*cross_sum for j in idx),F(0))
        margin=min(margin,2*h*nu/(1+h*norm/2)**2)
    return margin


def exchange_constants(model,vol,active,mass=MASS,charge=CHARGE):
    """Upper coefficient of sum of skew pair norms divided by sqrt(n_e)."""
    W=np.asarray(model['material_map']);me=model['energy_masses'][0];active=np.asarray(active,bool);n=len(vol)
    if W.shape!=(len(me),3*n) or active.shape!=(n,3):raise ValueError('exchange chart')
    out=[]
    for i in range(n):
        C=F(0)
        for e,k in zip(*np.nonzero(W[:,3*i:3*i+3])):
            for j in np.flatnonzero(active[i]):
                C+=sqrt_interval(q(W[e,3*i+k])**2*q(charge[j])**2/(q(me[e])*q(vol[i])*q(mass[j])))[1]
        out.append(C)
    return out


def tail_start_exact(certificate,constants,e_upper,alpha,dt):
    """Reverse-solve a sufficient exact tail clock with half-margin reserved.
    e_k <= min(e0,1/(k*h*alpha_min)); comparison block uses the actual current
    losses and no-birth events at each step, only exchanges are removed.
    """
    m=int(certificate['block_steps']);rho=F(certificate['rho_upper_exact']);h=q(dt);a=min(map(q,alpha))
    if m<1 or not 0<=rho<1 or min(h,a)<=0 or len(constants)!=len(e_upper):raise ValueError('tail margin chart')
    if any(q(v)<0 for v in list(constants)+list(e_upper)):raise ValueError('negative upper')
    C=sum((q(v) for v,e in zip(constants,e_upper) if q(e)>0),F(0));delta=(1-rho)/(2*m)
    d0=h*sum((q(v)*sqrt_interval(q(e))[1] for v,e in zip(constants,e_upper)),F(0))
    need=h*C*C/(a*delta*delta)
    k=0 if d0<=delta else max(1,ceil_div(need.numerator,need.denominator))
    return dict(start_step=k,block_steps=m,block_norm_upper_exact=str((1+rho)/2),
        uniform_step_exchange_upper_exact=str(delta),sufficient_start_seconds_exact=str(k*h),
        no_collision_limit_matching_required=True,exact_real_prefix_enclosure_required=True,physical_admission=False)


def certify_policy(material,cfg,pop_support,e_upper,theta_upper,powers=(32,48,64,80),bits=256):
    """Same original fixed atlas, exact field port, varying-current comparison.
    Population support and upper bounds are supplied for the exact tail start.
    Not a certificate of the computed prefix state or continuum geometry.
    """
    from solar_changing_tail import right_limit_reference
    from solar_spherical_geometry import geometry
    if not cfg.get('common_stage_atlas',False) or any(q(v)!=0 for v in cfg['kinetics']['ionization_s_inv']):raise ValueError('fixed birth-free atlas required')
    rows,neutral,D,gyro,axis=material;active=np.asarray(pop_support,bool);n=len(rows)
    if active.shape!=(n,3) or len(e_upper)!=n or len(theta_upper)!=n or any(q(v)<0 for v in list(e_upper)+list(theta_upper)) or np.any(active[:,0]!=active[:,1:].any(axis=1)):
        raise ValueError('charge-neutral support/upper chart')
    if any(bool(active[i,0])!=(q(e_upper[i])>0) for i in range(n)):raise ValueError('support and upper inconsistent')
    # Only the right support is read by the reference constructor.
    ref=right_limit_reference(material,cfg,active.astype(float));vol,_,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'],int(cfg.get('nested_depth',0)))
    h=ref['dt'];cm=uniform_current_margin(rows,neutral,theta_upper,gyro,axis,active,h)
    L=list(map(q,cfg.get('terminal_load_rate_s_inv',cfg['load_rate_s_inv'])))
    if len(L)!=ne or any(v<0 for v in L):raise ValueError('terminal load chart')
    p=q(cfg['source_coupling_sqrt_inv_s']);edge=int(cfg['source_edge'])
    if p<=0 or not 0<=edge<ne:raise ValueError('source chart')
    field_diag=[-v for v in L]+[F(0)]*nf;field_diag[edge]-=p*p
    cert=preconditioned_block_certificate(ref['generator'],h,ref['receipt'],ref['occupied'],ne+nf,bits,powers,field_diag,cm)
    constants=exchange_constants(ref['model'],vol,active)
    start=None if cert['certificate'] is None else tail_start_exact(cert['certificate'],constants,e_upper,cfg['kinetics']['recombination_m3_s'],h)
    return dict(reference=cert,tail_start=start,conditional_tail_decay_proved=start is not None,
        exact_fixed_binary_geometry=True,exact_affine_field_port=True,requires_real_prefix_population_temperature_enclosure=True,
        requires_exact_charge_neutral_birth_free_tail=True,physical_admission=False)
