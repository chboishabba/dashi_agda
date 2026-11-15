#!/usr/bin/env python3
"""Original a=t AdS5 frozen-wall oblique Neumann inverse, rigorously
bounded high positive-Laplace frequency, and low-s obstruction.

Exact reuse target: BalabanFiniteNeumannParametrix.agda,
BalabanWeightedNeumannRemainder.agda. This is a FROZEN symbol, NOT a
nonstationary Green function, a retarded boundary FIO or observed Weyl.
"""
import json
import math
from scipy.special import kve

def symbol(t, laplace_s, k):
    if not (1 <= t <= 2 and laplace_s > 0 and k >= 0):
        raise ValueError("Original t in [1,2], real s>0 and spatial |k|>=0")
    b=1/t
    v=-1/math.sqrt(1+t*t)
    q=math.hypot(laplace_s,k)
    x=q*b
    # Scaled K protects from underflow. K2=K0+2K1/x; K0<K1.
    Z=-kve(2,x)/(q*kve(1,x))
    R=-v*laplace_s*Z
    upper=abs(v)*(laplace_s/q)*(1+2/x)
    assert abs(R)<upper
    return dict(t=t,b=b,v=v,s=laplace_s,k=k,q=q,Z=Z,
                residual_multiplier_R=R,boundary_factor_A=1-R,
                exact_frozen_oblique_inverse=1/(1-R),
                upper_bound_on_abs_R=upper)

def frozen_finite(t=1,laplace_s=16,k=0,depth=128):
    if depth<0 or depth>1000: raise ValueError("Finite-depth parameter")
    r=symbol(t,laplace_s,k)
    R=r["residual_multiplier_R"]
    B=r["boundary_factor_A"]
    partial=(1-R**depth)/(1-R)
    left=1-B*partial
    right=R**depth
    assert abs(left-right)<max(2e-12,1e-10*abs(right))
    r.update(depth=depth,neumann_finite_approximation=partial,
             residual_from_operator=left,exact_residual_power=right,
             strict_contraction_here=bool(abs(R)<1),
             original_moving_retarded_operator_constructed=False,
             nonzero_original_receiver_Weyl_proved=False)
    return r

def uniform_original_high_s(s_min=16):
    if s_min<=0: raise ValueError("s_min must be positive")
    # q>=s, b>=1/2, |v|<=1/sqrt(2):
    # |R| < (1+4/s_min)/sqrt(2) on ALL original t,k.
    rho=(1+4/s_min)/math.sqrt(2)
    if rho>=1: raise ValueError("Uniform strict bound fails for this threshold")
    n=128
    bound=rho**n
    assert bound<1e-6
    sample=[symbol(t,s,k) for t in (1,1.2,1.5,1.8,2)
            for s in (s_min,2*s_min,10*s_min)
            for k in (0,1,10,s_min)]
    assert all(abs(d["residual_multiplier_R"])<rho for d in sample)
    return dict(t_interval="[1,2]",s_sector="real s>=16",k_sector="all |k|>=0",
        identity="K2(x)=K0(x)+2K1(x)/x, 0<K0(x)<K1(x)",
        uniform_rho=rho,strict_contraction=True,
        depth=n,uniform_residual_bound=bound,
        checked_grid_points=len(sample),
        applicable_operator="frozen-wall positive-real Laplace oblique boundary symbol only",
        lower_frequency_contraction=False,
        actual_time_dependent_boundary_FIO=False)

def low_frequency_counterexample():
    d=symbol(1,.05,0)
    a=abs(d["residual_multiplier_R"])
    assert a>1
    return dict(t=1,s=.05,k=0,abs_residual=a,
      frozen_neumann_series_diverges=True,
      actual_causal_AdS_Green_operator_disproved=False)

def audit():
    return dict(high=uniform_original_high_s(),
         low=low_frequency_counterexample(),
         one_example=frozen_finite(),
         original_time_dependent_neumann_to_weyl_proved=False,
         physical_graviton_observed=False)

if __name__=="__main__":print(json.dumps(audit(),indent=2,
                  default=lambda x:x.item() if hasattr(x,"item") else str(x)))
