#!/usr/bin/env python3
"""Original 5D AdS5 moving a=t brane: strict null convexity + lens-symbol ledger.

Stefanov--Yang, Analysis & PDE 11 (2018) 1381, DOI
10.2140/apde.2018.11.1381: 1+n (n>=2) Lorentzian DN lens FIO.
Uhlmann--Zhang JDE 309 (2022) Lemma 13 assumes 1+3 dimensions;
cannot automatically apply that Neumann lens lemma in 1+4.
DN FIO is NOT yet the original Neumann-to-Weyl composition.
"""
import json
import mpmath as mp
import sympy as s

def symbolic():
    v,vp,b=s.symbols('v vp b',real=True,finite=True)
    st=s.sqrt(1-v*v)
    # g=z^-2 diag(-1,1,1,1,1), boundary z=b(T), v=b'(T).
    # Domain z>=b(T); outward n_cov=(v,-1,0,0,0)/(b sqrt(1-v²)).
    # Tangent null L=(1,v,u), |u|²=1-v². Christoffel term cancels.
    DnuT=vp/(b*st**3)-v*v/(b*b*st)
    Dnuz=-v*vp/(b*st**3)+v/(b*b*st)
    kappa=s.simplify(DnuT+v*Dnuz)
    assert s.simplify(kappa-vp/(b*st))==0
    t=s.symbols('t',positive=True)
    vel=-1/s.sqrt(1+t*t)
    accel=t**3/(1+t*t)**2
    original=s.simplify(kappa.subs({v:vel,vp:accel,b:1/t}))
    assert s.simplify(original-t**3/(1+t*t)**s.Rational(3,2))==0
    return dict(outward_normal_covector='(v,-1,0,0,0)/(b sqrt(1-v²))',
       tangent_null='(1,v,u), |u|²=1-v²',
       outward_null_second_form='b_second_T/[b sqrt(1-v²)]',
       original_a_t_value='t³/(1+t²)^(3/2)',
       strict_null_convex_on_t_1_to_2=True,
       static_neumann_wall_strictly_null_convex=False)

def lens(t_obs=2,eps=.001,dt_emit=.0002):
    from ksw668_f8_non_glancing_source import audit
    r=audit(t_obs,eps,dt_emit)
    mp.mp.dps=60
    te=mp.mpf(str(r['actual_source_proper_t']))
    tr=mp.mpf(str(t_obs))
    convex=lambda t:t**3/(1+t*t)**mp.mpf('1.5')
    ce=convex(te);cr=convex(tr)
    assert 0<ce<cr
    ne=mp.mpf(str(r['emitter_normal_symbol']))
    nr=mp.mpf(str(r['receiver_normal_symbol']))
    # Pointwise principal factors only. Full lens transport is UNKNOWN.
    local_neumann_gain=1/abs(ne)
    reflection_factor=2
    polar=mp.mpf(str(r['TT_Qyy_for_x_ray']))
    weyl=mp.mpf(str(r['intrinsic_4D_Weyl_principal']))
    local_factor=local_neumann_gain*reflection_factor*polar*weyl
    E5=nr*nr/2  # SMS at source-free receiver: E5 = -deltaG4
    assert local_factor>0 and E5>0
    return dict(original_receiver_t=float(tr),source_t=float(te),
       emitter_outward_null_second_form=float(ce),
       receiver_outward_null_second_form=float(cr),
       source_normal_symbol=float(ne),receiver_normal_symbol=float(nr),
       local_formal_Neumann_source_factor=float(local_neumann_gain),
       homogeneous_Neumann_reflection_factor=reflection_factor,
       local_TT_polarization=float(polar),
       local_intrinsic_Weyl_principal=float(weyl),
       local_projected_5D_Weyl_principal=float(E5),
       SMS_receiver_outside_source=True,
       product_of_known_local_nonzero_symbol_magnitudes=float(local_factor),
       actual_global_5D_Lens_FIO_transport_amplitude_computed=False,
       actual_5D_Neumann_to_Weyl_composition_proved=False,
       source_to_original_receiver_nonzero_theorem_proved=False,
       input_null_lens_dimensionality='1+4 (Stefanov-Yang handles 1+n n>=2)',
       Uhlmann_Zhang_2022_original_dimensionality='1+3, requires 5D extension',
       quantitative_receiver_propagator_and_dynamics_remain_open=True)

def audit():
    return dict(symbolic=symbolic(),original_t2=lens(),
       stationary_control=dict(vprime=0,strict_convexity=False),
       FIO_transport_composition_accepted=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
