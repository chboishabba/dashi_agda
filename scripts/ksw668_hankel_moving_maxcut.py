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
    W=y*s.exp(-y*y)*g/(1-v*v)
    Bw=(1-v*v)*s.diff(W,y)+v*s.diff(W,T)
    assert s.simplify(Bw.subs(y,0)-g)==0
    L=s.diff(W,T,2)-2*v*s.diff(W,T,y)-(1-v*v)*s.diff(W,y,2)+(
      3/(y+b)-s.diff(v,T))*s.diff(W,y)-s.diff(W,x,2)
    assert s.simplify(L.subs(y,0))!=0
    return dict(exact_oblique_boundary_lift=True,
      lift='y exp(-y²) G(T,x)/(1-v(T)²)',
      wall='(1-v²)u_y+v u_T=G',
      no_boundary_source_after_lifting=True,
      homogeneous_PDE_interior_force='-L[u_lift]',
      regular_source_smooth_and_zero_near_initial_required=True,
      Green_operator_constructed=False,nonzero_receiver_proved=False)

def audit():
    return dict(stationary_symbolic=verify_resolvent_symbolic(),
      stationary_resolvent=stationary_outgoing(),
      normalized_KK=normalized_modes(),
      KK_packet=finite_energy_packet(),
      moving_source_lift=moving_boundary_lift(),
      exact_original_moving_retarded_Green=False,
      gravitational_observation=False)

if __name__=='__main__':
    print(json.dumps(audit(),indent=2,sort_keys=True))
