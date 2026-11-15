#!/usr/bin/env python3
"""Non-glancing ORIGINAL moving AdS5 compact-source microlocal preflight.

At the exact original t2/r_g receiver, identify an emitting spacetime point
strictly INSIDE a smooth compact TT source, and compute nonzero Neumann
normal and induced Weyl principal symbols. This is not yet the boundary
Poisson/FIO transport theorem, a matter action or an observed graviton.
"""
import json
import mpmath as mp

def F(t):
    return mp.asinh(t)-mp.sqrt(1+t*t)/t

def audit(t_obs=2,source_radius=.001,source_dt=.0002):
    if not (t_obs>1 and 0<source_radius<.1 and source_dt>0):
        raise ValueError("positive original source/receiver epoch required")
    mp.mp.dps=70
    t_obs=mp.mpf(str(t_obs))
    eps=mp.mpf(str(source_radius))
    dT=mp.mpf(str(source_dt))
    t_emit=mp.findroot(lambda t:F(t)-F(1)-dT,
                       1+dT/mp.sqrt(2))
    T_span=F(t_obs)-F(t_emit)
    dz=1/t_obs-1/t_emit
    ray_slope=dz/T_span
    r_origin=mp.sqrt((F(t_obs)-F(1))**2-(1/t_obs-1)**2)
    r_emit=mp.sqrt(T_span*T_span-dz*dz)
    x_emit=r_origin-r_emit
    v=lambda t:-1/mp.sqrt(1+t*t)
    normal=lambda t:(1/t)*(ray_slope-v(t))/mp.sqrt(1-v(t)**2)
    n_start,n_end=normal(t_emit),normal(t_obs)
    assert 0<x_emit<eps and n_start>0>n_end
    assert r_origin-eps>mp.log(t_obs)
    assert v(t_emit)<ray_slope<v(t_obs)
    # Convex moving wall -> straight null chord lies strictly in z>b(T).
    for i in range(1,100):
        tt=t_emit+(t_obs-t_emit)*mp.mpf(i)/100
        zline=1/t_emit+dz*(F(tt)-F(t_emit))/T_span
        assert zline>1/tt
    S=mp.sqrt(1+t_obs*t_obs)/t_obs
    kx=mp.sqrt(1-ray_slope*ray_slope)
    omega_eta=S*(1-v(t_obs)*ray_slope)
    weyl=(omega_eta**2+kx**2)/(4*t_obs*t_obs)
    assert weyl>0 and kx>0
    return dict(receiver_original_t=float(t_obs),
      original_receiver_comoving_r=float(r_origin),
      source_T_after_t1=float(dT),
      source_proper_t=float(t_emit),source_x=float(x_emit),
      source_ball_radius=float(eps),
      photon_dark_margin=float(r_origin-eps-mp.log(t_obs)),
      direct_ray_radial_slope=float(ray_slope),
      v_emitter=float(v(t_emit)),v_receiver=float(v(t_obs)),
      strict_inside_bulk_all_chord=True,
      emitter_normal_symbol=float(n_start),
      receiver_normal_symbol=float(n_end),
      TT_Qyy_for_x_ray=1.,
      spatial_wavevector_x=float(kx),
      intrinsic_4D_Weyl_principal=float(weyl),
      null_screen_Jacobi_no_focusing_in_constant_AdS=True,
      candidate_pulse="C-infinity compact spacetime oscillatory bump; local fourth-order TT projector, lambda^-4 normalization",
      boundary_Poisson_FIO_theorem_application_pending=True,
      microphysical_brane_action_supplied=False,
      actual_nonzero_smooth_compact_source_receiver_theorem_accepted=False,
      physical_graviton_observed=False)

if __name__=="__main__":
    print(json.dumps(dict(original_t2=audit(),
          longer_t6=audit(6,.024,.0035)),indent=2))
