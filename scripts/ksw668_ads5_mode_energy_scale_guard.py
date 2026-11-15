#!/usr/bin/env python3
"""KSW B5/C1 original AdS5 non-finite Bessel basis and conditional SI scaling.

Rescaling ALL coordinates by ell is a change of units for the original
a(t)=t source, not a realistic modern-cosmology or laboratory prediction.
A plane-wave Bessel tensor mode is not a localized finite-energy pulse.
"""
import json, math
import mpmath as mp
import sympy as s

C=299792458
def audit(ell_m=1.):
    if not math.isfinite(ell_m) or ell_m<=0:
        raise ValueError('Positive SI AdS length required')
    mp.mp.dps=40
    T=lambda t:mp.asinh(t)-mp.sqrt(1+t*t)/t
    rg=mp.sqrt((T(2)-T(1))**2-mp.mpf('.5')**2)
    advance=mp.exp(rg)-2
    assert 0<advance and abs(advance-mp.mpf('.009322862731128'))<mp.mpf('1e-10')
    # Fixed brane receiver: instantaneous proper phase omega(t)
    # =sqrt(2)*T_b'(t)*c/ell, not constant bulk omega.
    f1=C/(mp.pi*ell_m)
    f2=mp.sqrt(10)*C/(8*mp.pi*ell_m)
    z=s.symbols('z',positive=True)
    assert s.simplify(s.diff(z*z*s.besselj(2,z),z)-z*z*s.besselj(1,z))==0
    # Time-averaged z^-3 tensor energy per radial z:
    # e(z)=z/4 [3 J2(z)^2+J1(z)^2].
    # By the standard Bessel asymptotic, average e(z)->1/pi
    # as z increases; the radial integral diverges linearly.
    fun=lambda x:x*(3*mp.besselj(2,x)**2+mp.besselj(1,x)**2)/4
    pts=[mp.mpf(1)+j*mp.pi for j in range(25)]
    integrated=mp.fsum(mp.quad(fun,[a,b]) for a,b in zip(pts,pts[1:]))
    slope=integrated/(pts[-1]-pts[0])
    assert abs(slope-1/mp.pi)<mp.mpf('.015')
    return dict(status='PASS conditional scaling and infinite-radial-energy Bessel basis control',
                ell_metres=ell_m,
                dimensionless_same_receiver_clock_advance=float(advance),
                clock_advance_seconds_only_if_all_source_geometry_rescaled=float(advance*ell_m/C),
                source_Hubble_t1_per_second=C/ell_m,source_Hubble_t2_per_second=C/(2*ell_m),
                manufactured_mode_receiver_phase_f_t1_Hz=float(f1),
                manufactured_mode_receiver_phase_f_t2_Hz=float(f2),
                time_averaged_radial_energy_density='z/4*(3 J2(z)^2+J1(z)^2)',
                average_large_z_energy_per_radial_z=float(slope),
                exact_asymptotic_average='1/pi',
                finite_energy_Bessel_separated_mode=False,
                calibrated_GW_detector_band=False,GW170817_implied_ell_bound=False,
                localized_retarded_TT_pulse=False)
if __name__=='__main__':
    print(json.dumps(audit(),indent=2,sort_keys=True))
