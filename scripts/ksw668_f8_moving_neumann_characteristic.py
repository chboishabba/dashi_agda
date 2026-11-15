#!/usr/bin/env python3
"""Original moving AdS5 a=t tensor Israel Neumann boundary in q± coordinates.

q+=H_T+H_z outgoing to the wall; q-=H_T-H_z incoming to the bulk.
No repeated reflections, global FIO, or observed signal is assumed.
"""
import json,math
def exact(t,q_plus=1.,g=0.):
    if not 1<=t<=2:raise ValueError("Original proper t interval")
    v=-1/math.sqrt(1+t*t)
    beta=(1+v)/(1-v)
    incoming=beta*q_plus-2*g/(1-v)
    check=(1+v)*q_plus+(v-1)*incoming
    assert math.isclose(check,2*g,abs_tol=1e-12,rel_tol=1e-12)
    return dict(t=t,wall_v=v,beta=beta,q_plus=q_plus,
       q_minus=incoming,source_g=g,
       q_plus_advection_velocity=-(1+v),
       q_minus_advection_velocity=1-v,
       original_Israel_boundary_exact=True,
       moving_retarded_Green_constructed=False)
def bound():
    lower=(math.sqrt(2)-1)**2
    upper=(3-math.sqrt(5))/2
    samples=[exact(1+i/100) for i in range(101)]
    assert all(lower-1e-14<=r["beta"]<=upper+1e-14 for r in samples)
    assert math.isclose(exact(4/3)["beta"],.25,abs_tol=1e-15)
    for r in samples:
        v=r["wall_v"];p=r["q_plus"];m=r["q_minus"]
        assert math.isclose((1-v)*m*m/((1+v)*p*p),
                            r["beta"],rel_tol=1e-12)
    return dict(t_interval="[1,2]",exact_beta_formula="(sqrt(1+t²)-1)/(sqrt(1+t²)+1)",
       lower=lower,upper=upper,t_4over3_exact_beta="1/4",
       samples=len(samples),homogeneous_flux_ratio_equals_beta=True,
       no_repeated_boundary_reflections_assumed=True,
       actual_global_source_to_receiver_FIO=False)
def audit():return dict(bound=bound(),rational_slice=exact(4/3,1/8,1/12),
                        physical_graviton_observed=False)
if __name__=="__main__":print(json.dumps(audit(),indent=2))
