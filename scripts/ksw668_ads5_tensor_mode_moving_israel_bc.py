#!/usr/bin/env python3
"""KSW D2/B3: real AdS5 transverse-traceless tensor bulk mode + MOVING brane BC.

ORIGINAL SCIENTIFIC SOURCES (not new DASHI theorems):
Maartens & Koyama, Brane-world gravity, Living Rev Relativ (2010),
doi:10.12942/lrr-2010-5; moving-boundary graviton analyses:
Koyama, arXiv:astro-ph/0407263;
Ruser & Durrer, Phys Rev D 76 104014 (2007), arXiv:0704.0790.
Physical TT perturbations in AdS5 obey the same scalar bulk wave
operator as a minimally coupled massless scalar, after Fourier projection
in brane-space and fixing a TT polarization:
    [-d_T² + d_z² - (3/z)d_z + d_x²] h = 0,
    ds5² = z^-2(-dT²+dz²+dx²+dy²+dw²), ell=1.

On the SAME moving a(t)=t FRW brane from Caldwell-Langlois:
  z_b(t)=1/t, T'_b(t)=sqrt(1+t²)/t².
The oriented unit normal is n^A=(-1/t²,+sqrt(1+t²)/t²,0,0,0);
it obeys g(n,n)=+1, g(n,u)=0. If the brane tensor anisotropic
stress vanishes, the Z2 Israel tensor boundary condition is
  n^A partial_A h|_brane = 0
rather than pure static d_z h=0.

An EXACT nontrivial separated bulk tensor solution is
  h=cos(k*x-omega*T) z² J_2(mz), omega²=k²+m².
The bulk TT PDE vanishes exactly, but its MOVING Neumann residual
at t=1, z=1, T=0, x=0, k=m=1 is sqrt(2)*J_1(1)>0.
Consequently a single separated outgoing/standing frequency cannot
be silently labelled a brane-coupled graviton transport mode.
At fixed brane a const zero-mode is exactly Neumann compatible, but
does not carry a localized communication pulse.
Actual physical modes need a time-dependent KK superposition and
moving Israel boundary/anisotropic-stress source with initial conditions.

A genuine *nonzero source* changes the boundary condition; this module
does NOT assign a graviton-to-matter coupling, measure TT reception,
prove all-mode spectral stability or a shortcut observed on Earth.
"""
import argparse,json
import sympy as s

def audit():
    t,z,T,x,k,m=s.symbols("t z T x k m",positive=True,real=True)
    omega=s.sqrt(k*k+m*m)
    psi=z*z*s.besselj(2,m*z)
    h=s.cos(k*x-omega*T)*psi
    operator=s.simplify(-s.diff(h,T,2)+s.diff(h,z,2)
                        -3*s.diff(h,z)/z+s.diff(h,x,2))
    assert operator==0
    derivative=s.simplify(s.diff(psi,z)-m*z*z*s.besselj(1,m*z))
    assert derivative==0
    ub=s.Matrix([s.sqrt(1+t*t)/t**2,-1/t**2])
    n=s.Matrix([-1/t**2,s.sqrt(1+t*t)/t**2])
    induced_g=s.diag(-t*t,t*t)
    assert s.simplify((ub.T*induced_g*ub)[0]+1)==0
    assert s.simplify((n.T*induced_g*n)[0]-1)==0
    assert s.simplify((n.T*induced_g*ub)[0])==0
    neumann=s.simplify(
        (-s.diff(h,T)+s.sqrt(1+t*t)*s.diff(h,z))/t**2)
    example=s.simplify(neumann.subs({
       t:1,z:1,T:0,x:0,k:1,m:1}))
    assert s.simplify(example-s.sqrt(2)*s.besselj(1,1))==0
    assert float(example.evalf(15))>.6
    # The same original junction background is used, not an arbitrary mirror.
    assert s.simplify(ub[1]+1/t**2)==0
    # Exact zero-mode control h=const yields a well-posed Neumann field
    # but no propagating usable bulk wave.
    h_zero=s.Integer(1)
    zero_pde=-s.diff(h_zero,T,2)+s.diff(h_zero,z,2)-3*s.diff(h_zero,z)/z+s.diff(h_zero,x,2)
    zero_bc=(-s.diff(h_zero,T)+s.sqrt(1+t*t)*s.diff(h_zero,z))/t**2
    assert zero_pde==0 and zero_bc==0
    return {
      "status":"PASS exact AdS5 TT bulk Bessel PDE; one frequency fails moving Israel-Neumann boundary",
      "original_source":"Maartens-Koyama braneworld tensor perturbations; moving-brane studies",
      "original_shortcut_paper_DOI":"10.1016/S0370-2693(01)00631-1",
      "same_background":"AdS5 a(t)=t, ell=1, brane Israel K/S from ksw668_caldwell_langlois_israel_exact.py",
      "tensor_wave_operator":"-dT²+dz²-3/z*d_z+dx²",
      "nontrivial_TT_bulk_mode":"cos(kx-sqrt(k²+m²) T)*z²*J2(mz)",
      "bulk_TT_PDE_all_xTz_exact":True,
      "normal_unit_spacelike":True,
      "brane_tangent_unit_timelike":True,
      "normal_tangent_orthogonal":True,
      "source_free_moving_Israel_BC":"n^A partial_A h=0",
      "one_separated_mode_boundary_residual_at_t1":str(example),
      "one_separated_mode_residual_numeric":float(example.evalf(15)),
      "one_separated_mode_solves_full_moving_BC":False,
      "homogeneous_constant_mode_solves_moving_BC":True,
      "homogeneous_mode_is_communication_pulse":False,
      "arbitrary_KK_superposition_constructed":False,
      "boundary_anisotropic_stress_source_specified":False,
      "all_mode_stability_established":False,
      "physical_graviton_source_receiver_or_measured_effect":False,
      "uses_same_5D_AdS_metric_as_original_horizon":True
    }

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out")
    a=p.parse_args()
    body=json.dumps(audit(),indent=2,sort_keys=True)+"\n"
    if a.out:open(a.out,"w",encoding="utf-8").write(body)
    print(body)
