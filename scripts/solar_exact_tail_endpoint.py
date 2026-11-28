"""Certified source-off restoration and finite remainder on exact binary-input
finite split geometry, with no measured/continuum promotion.
"""
from fractions import Fraction as F
from solar_event_rounding import q,sqrt_interval
from solar_tail_dyadic import ceil_div
from solar_material_interval import exact_material_prefix
from solar_exact_tail_policy import certify_policy
from solar_spherical_geometry import geometry


def ceil(x):return ceil_div(x.numerator,x.denominator)


def remainder(prefix,policy,material,cfg,vol,k):
    """All additional net work after k tail steps is in [0, upper].
    No tail tariff, forcing, births or external material control.
    """
    if int(k)!=k or k<0 or not policy['conditional_tail_decay_proved'] or not prefix['initial_population_zero'] or not prefix['exact_charge_neutral']:
        raise ValueError('unadmitted exact tail')
    k=int(k);h=q(float(cfg['period_s'])/len(cfg['incident_sqrt_W']));a=min(map(q,cfg['kinetics']['recombination_m3_s']))
    start=policy['tail_start'];rho=F(start['block_norm_upper_exact']);m=start['block_steps']
    blocks=max(0,(k-start['start_step'])//m)
    energy=F(prefix['field_energy_upper_J'])/(1+blocks*(1-rho))**2
    e=[F(v)/(1+k*h*a*F(v)) for v in prefix['electron_upper']]
    theta=[F(v)/(1+k*h*q(c)/q(cap)) for v,c,cap in zip(prefix['temperature_upper'],cfg['cooling_W_K'],cfg['heat_capacity_J_K'])]
    chem=list(map(q,cfg['kinetics']['formation_J_per_particle']));eta=q(cfg['kinetics']['chemical_recovery_efficiency'])
    formation=sum((q(V)*v*(chem[0]+max(chem[1:])) for V,v in zip(vol,e)),F(0))
    return dict(tail_steps=k,certified_blocks=blocks,field_energy_upper_J=str(energy),
        field_norm_upper=str(sqrt_interval(2*energy)[1]),population_norm_upper=str(sqrt_interval(2*sum((v*v for v in e),F(0)))[1]),
        pool_norm_upper=str(sqrt_interval(sum((v*v for v in e),F(0)))[1]),
        thermal_norm_upper=str(sqrt_interval(sum((v*v for v in theta),F(0)))[1]),
        additional_net_interval_J=['0',str(energy+eta*formation)],physical_admission=False)


def tolerance_clock(prefix,policy,material,cfg,vol,atol):
    """Conservative exact reverse clock using L1 material bounds and block decay."""
    tol=list(map(q,atol))
    if len(tol)!=4 or min(tol)<=0:raise ValueError('positive finite tolerances required')
    h=q(float(cfg['period_s'])/len(cfg['incident_sqrt_W']));a=min(map(q,cfg['kinetics']['recombination_m3_s']))
    start=policy['tail_start'];rho=F(start['block_norm_upper_exact']);m=start['block_steps']
    field=sqrt_interval(2*F(prefix['field_energy_upper_J']))[1]
    j=max(0,ceil((field/tol[0]-1)/(1-rho)))
    n=sum(F(v)>0 for v in prefix['electron_upper']);t=sum(map(F,prefix['temperature_upper']),F(0))
    lam=min(q(c)/q(cap) for c,cap in zip(cfg['cooling_W_K'],cfg['heat_capacity_J_K']))
    k=max(start['start_step']+j*m,ceil(2*n/(h*a*tol[1])),ceil(n/(h*a*tol[2])),ceil(t/(h*lam*tol[3])),0)
    r=remainder(prefix,policy,material,cfg,vol,k)
    for key,v in zip(('field_norm_upper','population_norm_upper','pool_norm_upper','thermal_norm_upper'),tol):
        if F(r[key])>v:raise ArithmeticError('reverse clock failed rational check')
    return dict(sufficient_tail_steps=k,sufficient_seconds_exact=str(k*h),endpoint_remainder=r,
        finite_tolerance_exact_return_distinguished=True,physical_admission=False)


def exact_endpoint(material,cfg,powers=(48,64,80),bits=256,atol=None):
    """Return proof receipt for zero-initial, charge-neutral birth-free tail.
    Exact real arithmetic of fixed binary geometry and input constants only.
    No validation of rounded prefix trajectory or independent physical ports.
    """
    vol,_,_,_=geometry(cfg['radii_m'],cfg['angular_level'],int(cfg.get('nested_depth',0)))
    prefix=exact_material_prefix(material,cfg,vol)
    result=dict(prefix=prefix,exact_finite_split_asymptotic_return=False,physical_admission=False)
    if not prefix['exact_charge_neutral'] or not prefix['initial_population_zero'] or not prefix['support_known']:
        result['status']='EXACT_ORIGINAL_MATERIAL_RETURN_NOT_ADMITTED';return result
    if any(q(v)!=0 for v in cfg['kinetics']['ionization_s_inv']) or min(map(q,cfg['kinetics']['recombination_m3_s']))<=0:
        result['status']='BIRTH_FREE_TAIL_NOT_ADMITTED';return result
    policy=certify_policy(material,cfg,prefix['population_support'],prefix['electron_upper'],prefix['temperature_upper'],powers,bits)
    result['tail_policy']=policy
    if not policy['conditional_tail_decay_proved']:
        result['status']='NO_CERTIFIED_BLOCK';return result
    result['exact_finite_split_asymptotic_return']=True
    result['status']='EXACT_FIXED_BINARY_GEOMETRY_ASYMPTOTIC_RETURN'
    result['tail_remainder_at_start']=remainder(prefix,policy,material,cfg,vol,0)
    paid_lo,paid_hi=map(F,prefix['paid_J']);aux=int(cfg['max_cycles'])*q(cfg['auxiliary_J']);incident=F(prefix['incident_J'])
    # Exact passive event and port identities, zero initial storage and exact
    # asymptotic restoration: incident is an upper bound on net work. The
    # crude lower bound credits no useful output or future chemical recovery.
    result['asymptotic_net_interval_J']=[str(-paid_hi-aux),str(incident-aux)]
    if atol is not None:result['finite_tolerance']=tolerance_clock(prefix,policy,material,cfg,vol,atol)
    return result
