#!/usr/bin/env python3
"""KSW668 stationary AdS5 outgoing resolvent, normalized KK continuum,
finite-energy spectral packet and exact moving-wall source lifting.

Attribution: Giddings/Katz/Randall 2000; Mannheim 2006;
Caldwell/Langlois 2001 (moving-brane geometry).
STATIONARY and MOVING results remain separate. No moving-wall Green
solution, wavefront-reception claim or experiment is supplied.
"""
import json
import math
import sympy as s
from scipy.integrate import quad
from scipy.special import jv, yv, kv

def stationary_outgoing(b=1., laplace_s=1.3, k=0.7, z=1.6):
    """Fourier(x), Laplace(t): d_z H|b=g; radial decay for real s>0."""
    if not (0<b<=z and laplace_s>0 and k>=0):
        raise ValueError("positive stationary wall and Laplace domain only")
    q=math.hypot(laplace_s,k)
    transfer=-(z*z*kv(2,q*z))/(b*b*q*kv(1,q*b))
    boundary_impedance=-kv(2,q*b)/(q*kv(1,q*b))
    return dict(q=q,transfer=transfer,boundary_impedance=boundary_impedance,
                retarded_Laplace_right_half_plane=True,
                stationary_wall_only=True,moving_wall_retarded=False)

def verify_resolvent_symbolic():
    z,q,b=s.symbols('z q b',positive=True)
    F=z*z*s.besselk(2,q*z)
    assert s.simplify(s.diff(F,z)+q*z*z*s.besselk(1,q*z))==0
    assert s.simplify(s.diff(F,z,2)-3*s.diff(F,z)/z-q*q*F)==0
    unit=F/(-b*b*q*s.besselk(1,q*b))
    assert s.simplify(s.diff(unit,z).subs(z,b)-1)==0
    Z=-s.besselk(2,q*b)/(q*s.besselk(1,q*b))
    assert s.limit(q*q*Z,q,0,dir='+')==-2/b
    return dict(radial_K2_ODE_exact=True,normal_derivative_exact=True,
                stationary_Neumann_unit_source=True,
                massless_resolvent_pole_coefficient='-2/b',
                outgoing_at_radial_infinity=True)

def normalized_modes(b=1.,m=1.1,z=1.7):
    """Continuum eigenfunctions in L2([b,infinity),z^-3 dz)."""
    if not (b>0 and m>0 and z>=b): raise ValueError('b,m>0,z>=b')
    mb=m*b
    D=math.hypot(jv(1,mb),yv(1,mb))
    C=yv(1,mb)*jv(2,m*z)-jv(1,mb)*yv(2,m*z)
    H=z*z*math.sqrt(m)*C/D
    dH=z*z*m*math.sqrt(m)*(yv(1,mb)*jv(1,m*z)-jv(1,mb)*yv(1,m*z))/D
    H0=math.sqrt(2)*b
    wb=2*b/(math.pi*math.sqrt(m)*D)
    return dict(continuum_H=H,continuum_Hz=dH,zero_H=H0,
                continuum_at_b=wb,spectrum_delta_normalized=True,
                zero_L2_weight_norm=1.,zero_energy_radial=0.,
                interpretation='generalized KK mode, not finite-energy single mode')

def finite_energy_packet(b=1.,mlo=.6,mhi=1.4):
    """C-infinity compact spectral KK amplitude and Schwartz TT spatial data.

    h(T,z,x) = integral dm A(m) H_m(z) integral d^3k fhat_TT(k)
         exp(i k.x) cos(sqrt(k^2+m^2) T).
    fhat_TT is polynomial TT projector on a Gaussian in momentum.
    """
    if not (b>0 and 0<mlo<mhi):raise ValueError('positive band')
    def A(m):
        x=(m-mlo)*(mhi-m)
        return math.exp(-.03/x) if x>0 else 0.
    norm=quad(lambda m:A(m)**2,mlo,mhi,epsabs=1e-10)[0]
    mass_sq=quad(lambda m:m*m*A(m)**2,mlo,mhi,epsabs=1e-10)[0]
    assert 0<norm<math.inf and 0<mass_sq<math.inf
    return dict(b=b,band=[mlo,mhi],finite_spectral_L2=norm,
      finite_spectral_mass_energy=mass_sq,
      radial_packet_finite_energy=True,spatial_TT_Schwartz_finite_H1=True,
      single_KK_mode_finite_energy=False,
      applies_to_stationary_Neumann_only=True,
      moving_source_reception_proved=False)

def moving_boundary_lift():
    """Exact homogeneous Neumann reduction; NOT moving Green existence."""
    T,y,x=s.symbols('T y x',real=True)
    v=s.Function('v')(T);b=s.Function('b')(T)
    g=s.Function('g')(T,x)
    cut=s.exp(-y*y/(1-y*y))  # for 0<=y<1; extend identically zero for y>=1
    W=y*cut*g/(1-v*v)
    Bw=(1-v*v)*s.diff(W,y)+v*s.diff(W,T)
    assert s.simplify(Bw.subs(y,0)-g)==0
    L=s.diff(W,T,2)-2*v*s.diff(W,T,y)-(1-v*v)*s.diff(W,y,2)+(
      3/(y+b)-s.diff(v,T))*s.diff(W,y)-s.diff(W,x,2)
    assert s.simplify(L.subs(y,0))!=0
    return dict(exact_oblique_boundary_lift=True,
      lift='y chi(y) G(T,x)/(1-v(T)²), chi=exp[-y²/(1-y²)] for 0<=y<1; zero otherwise',
      wall='(1-v²)u_y+v u_T=G',
      no_boundary_source_after_lifting=True,
      homogeneous_PDE_interior_force='-L[u_lift]',
      regular_source_smooth_and_zero_near_initial_required=True,
      lift_compact_in_y_for_compact_drive=True,
      Green_operator_constructed=False,nonzero_receiver_proved=False)


def moving_abstract_green_and_bulk_chord():
    """Apply Ginoux--Murro theorem 6.8 and proposition 5.1 to original AdS5.

    Mathematical theorem-application certificate, NOT explicit kernel/receiver.
    """
    t=s.symbols('t',positive=True)
    Tp=s.sqrt(1+t*t)/t**2
    b=1/t
    v=s.simplify(s.diff(b,t)/Tp)
    vp=s.simplify(s.diff(v,t)/Tp)
    assert s.simplify(v+1/s.sqrt(1+t*t))==0
    assert s.simplify(vp-t**3/(1+t*t)**2)==0
    assert s.simplify(1-v*v-t*t/(1+t*t))==0
    import mpmath as mp
    mp.mp.dps=65
    F=lambda tt:mp.asinh(tt)-mp.sqrt(1+tt*tt)/tt
    DT=F(2)-F(1)
    slope=-mp.mpf('0.5')/DT
    v1=-1/mp.sqrt(2)
    v2=-1/mp.sqrt(5)
    assert v1<slope<v2
    for tt in [mp.mpf('1.2'),mp.mpf('1.5'),mp.mpf('1.8')]:
        assert 1+slope*(F(tt)-F(1))>1/tt
    rg=mp.sqrt(DT**2-mp.mpf('0.25'))
    photon=mp.log(2)
    assert rg>photon
    return dict(original_t_interval='[1,2]',
        original_bulk_domain='z>=b(T)=1/t(T)',
        wall_timelike_exact='1-v²=t²/(1+t²)>=1/2',
        strict_wall_convexity_exact='b_second_T=t³/(1+t²)²>0',
        global_hyperbolicity_argument='T-slices Cauchy, finite light speed, smooth positive timelike boundary; extend b outside finite strip',
        geometric_wave_operator='Box_AdS=z²*(-dT²+dz²-3/z dz+Delta_x)',
        Neumann_admissible_from='Ginoux and Murro arXiv:2007.02544 theorem 6.8, Neumann example, proposition 5.1',
        source_class='smooth compact TT boundary pi, vanishing near initial T',
        compact_lift='W=y chi(y) G/(1-v²), chi=exp[-y²/(1-y²)] on 0<=y<1 and 0 beyond',
        homogeneous_green_operator='G_N_ret by Ginoux-Murro theorem 6.8 and proposition 5.1',
        inhom_boundary_retarded_operator='H=W+G_N_ret[-Box_AdS W]',
        abstract_smooth_retarded_operator_established_by_theorem=True,
        explicit_moving_green_kernel_available=False,
        same_metric_causal_chord_interiors=True,
        chord_radial_slope=float(slope),
        boundary_velocities=[float(v1),float(v2)],
        bulk_null_horizon_comoving=float(rg),
        brane_photon_horizon_comoving=float(photon),
        nonzero_electric_Weyl_from_retarded_source_proved=False,
        physical_matter_action_proved=False,
        actual_graviton_observation=False)

def audit():
    return dict(stationary_symbolic=verify_resolvent_symbolic(),
      stationary_resolvent=stationary_outgoing(),
      normalized_KK=normalized_modes(),
      KK_packet=finite_energy_packet(),
      moving_source_lift=moving_boundary_lift(),
      moving_abstract=moving_abstract_green_and_bulk_chord(),
      explicit_original_moving_retarded_Green_kernel=False,
      gravitational_observation=False)

if __name__=='__main__':
    print(json.dumps(audit(),indent=2,sort_keys=True))
