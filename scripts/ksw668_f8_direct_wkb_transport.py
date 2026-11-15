#!/usr/bin/env python3
"""Original moving AdS5 direct-ray WKB tensor transport and Weyl principal ledger.

Stefanov--Yang (2018) Theorems 3.1,4.2 are general 1+n Lorentzian DN
FIO inputs; conversion to full Neumann-to-Weyl and global remainder control
is a separate mathematical weld. Not a graviton experiment.
"""
import json
import mpmath as mp
import sympy as s
from ksw668_f8_non_glancing_source import audit as ray
from ksw668_f8_null_convex_lens import lens

def symbolic():
    z,ze,slope,kx,T,x,lam=s.symbols('z ze slope kx T x lam',positive=True,real=True)
    phase=-T+slope*z+kx*x
    a0=z**s.Rational(3,2)
    H=s.exp(s.I*lam*phase)*a0
    L=lambda f:-s.diff(f,T,2)+s.diff(f,z,2)-3*s.diff(f,z)/z+s.diff(f,x,2)
    expr=s.simplify(L(H)/H)
    assert s.simplify(expr-lam**2*(1-slope**2-kx**2)+s.Rational(15,4)/z**2)==0
    assert s.simplify(expr.subs(kx**2,1-slope**2)+s.Rational(15,4)/z**2)==0
    a1=z**s.Rational(3,2)*s.Rational(15,8)/slope*(1/ze-1/z)
    transport=lambda a:2*slope*s.diff(a,z)-3*slope*a/z
    Lrad=lambda a:s.diff(a,z,2)-3*s.diff(a,z)/z
    assert s.simplify(transport(a0))==0
    assert s.simplify(transport(a1)+Lrad(a0))==0
    assert s.simplify(Lrad(a1))!=0
    return dict(phase='-T+slope*z+kx*x',
      null_eikonal='slope²+kx²=1',
      direct_tensor_WKB_amplitude='z^(3/2)',
      exact_leading_residual='-15/(4z²)*H',
      next_transport_amplitude='a1=z^(3/2)*15/(8*slope)*(1/ze-1/z)',
      order_lambda_zero_curvature_residual_canceled=True,
      remaining_residual='Lrad[a1]/(i lambda)',
      full_Neumann_FIO_error_bound_accepted=False)

def original_receiver():
    r=ray();l=lens();mp.mp.dps=60
    te=mp.mpf(str(r['actual_source_proper_t']))
    ze=1/te;zr=mp.mpf('.5')
    transport=(zr/ze)**mp.mpf('1.5')
    ne=mp.mpf(str(r['emitter_normal_symbol']))
    nr=mp.mpf(str(r['receiver_normal_symbol']))
    W4=mp.mpf(str(l['local_intrinsic_Weyl_principal']))
    W5=nr*nr/2
    # Physical prescribed TT boundary pi amplitude 1, n.dH=-6 pi.
    # Incident Neumann H is lambda^-1[-6/(i n_e.xi_e)] and
    # receiver homogeneous-Neumann trace is 2*incident.
    Hmag=12*transport/abs(ne)
    E4=Hmag*W4;E5=Hmag*W5
    assert min(transport,Hmag,E4,E5)>0
    return dict(emitted_z=float(ze),receiver_z=float(zr),
       direct_ray_transport=float(transport),
       per_unit_source_H_principal_times_lambda=float(Hmag),
       intrinsic_4D_Weyl_principal_per_lambda=float(E4),
       projected_5D_Weyl_principal_per_lambda=float(E5),
       source_normal_symbol=float(ne),receiver_normal_symbol=float(nr),
       Neumann_trace_reflection_factor=2,
       original_t2_photon_dark=True,
       source='smooth compact spacetime oscillatory bump, local fourth-order TT projector normalized by (lambda*kx)^4',
       finite_energy_for_every_fixed_source_frequency=True,
       full_5D_Neumann_to_Weyl_FIO_composition_and_error_written=False,
       source_generated_by_matter_action=False,
       physical_graviton_observed=False)

def audit():return dict(symbolic=symbolic(),original_t2=original_receiver())
if __name__=='__main__':print(json.dumps(audit(),indent=2))
