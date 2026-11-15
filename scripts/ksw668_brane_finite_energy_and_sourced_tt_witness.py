#!/usr/bin/env python3
"""KSW brane max-cut: finite-energy compact scalar emitter plus sourced TT boundary witness.

This extends existing PR #1504 owners, without claiming a retarded graviton.
Cylinder: finite-thickness ambient emitter near cylindrical brane, compact H1 spatial profile and triangular temporal
drive; classical finite-energy retarded wave by the energy estimate.
AdS5: nontrivial exact TT bulk Bessel mode with the *required* nonzero
Israel-normal source calculated on the same moving a=t brane. The latter
is an inverse boundary-source witness, not a local finite-energy retarded
emission or normalized detector prediction.
"""
import json
import math
import sympy as sp

def profile(u):
    return (15.0/16.0)*(1-u*u)**2 if abs(u)<1.0 else 0.0

def legendre5():
    p=math.sqrt(5.0-2.0*math.sqrt(10.0/7.0))/3.0
    q=math.sqrt(5.0+2.0*math.sqrt(10.0/7.0))/3.0
    wp=(322.0+13.0*math.sqrt(70.0))/900.0
    wq=(322.0-13.0*math.sqrt(70.0))/900.0
    return ((-q,wq),(-p,wp),(0.0,128.0/225.0),(p,wp),(q,wq))

def ramp(t,d):
    if t<=d: return 0.0
    return math.sqrt((t-d)*(t+d))/(4.0*math.pi**2*d*d)

def cylinder_audit(eps=0.02, t=2.125, tau=0.25):
    if not (0<eps<0.05 and 2+2*eps<t<math.pi and 0<tau and t-tau<2-2*eps):
        raise ValueError("Parameters must give strictly positive first-ramp response on entire source support")
    # 4D spatial source rho_eps(X)=prod_i 15/(16 eps)*(1-(X_i/eps)^2)^2
    # on |X_i|<eps, zero otherwise: compact support, rho in H1 and L2.
    # q(t)=t_+ -2(t-tau)_+ +(t-2tau)_+ : compact support and L1 integral tau^2.
    # Energy E(t) <= 1/2 (tau^2 * ||rho_eps||_L2)^2, zero initial data.
    # Integral of 1D squared normalized profile is (5/7)/eps.
    oneD_L2_sq=sp.Rational(5,7)/sp.Rational(str(eps))
    fourD_L2_sq=oneD_L2_sq**4
    energy_upper=sp.Rational(1,2)*sp.Rational(str(tau))**4*fourD_L2_sq
    nodes=legendre5()
    response=0.0
    min_distance=10.0
    max_distance=0.0
    for a,wa in nodes:
      for b,wb in nodes:
       for c,wc in nodes:
        for d,wd in nodes:
         distance=math.sqrt((2-eps*a)**2+eps*eps*(b*b+c*c+d*d))
         min_distance=min(min_distance,distance)
         max_distance=max(max_distance,distance)
         weight=wa*wb*wc*wd*profile(a)*profile(b)*profile(c)*profile(d)
         response+=weight*(ramp(t,distance)-2*ramp(t-tau,distance)+ramp(t-2*tau,distance))
    assert min_distance>2-2*eps and max_distance<2+2*eps
    assert min_distance<t and t-tau<min_distance and t<math.pi
    assert response>0
    # A robust positive pointwise lower bound on whole compact support:
    d_lo=2-eps
    d_hi=math.sqrt((2+eps)**2+3*eps**2)
    assert d_hi<t and t-tau<d_lo
    lower=math.sqrt(t*t-d_hi*d_hi)/(4*math.pi**2*d_hi*d_hi)
    assert lower>0 and response>=lower
    return dict(finite_spatial_L2_and_H1=True, temporal_source_compact=True,
                retarded_zero_initial_energy_upper=float(energy_upper),
                photon_first_arrival=math.pi, receiver_time=t,
                spatial_source_halfwidth=eps, numerical_receiver_response=response,
                rigorous_positive_receiver_lower=lower,
                finite_energy_early_scalar_receiver=True,
                exactly_thin_brane_confined_source=False,
                scalar_test_field_only=True, gravitational_backreaction=False)

def ads_tensor_audit():
    t,z,T,x,k,m=sp.symbols('t z T x k m',positive=True,real=True)
    omega=sp.sqrt(k*k+m*m)
    psi=z*z*sp.besselj(2,m*z)
    h=sp.cos(k*x-omega*T)*psi
    wave=sp.simplify(-sp.diff(h,T,2)+sp.diff(h,z,2)-3*sp.diff(h,z)/z+sp.diff(h,x,2))
    assert wave==0
    # True moving-brane unit-normal derivative; must equal source function.
    required_source=sp.simplify((-sp.diff(h,T)+sp.sqrt(1+t*t)*sp.diff(h,z))/t**2)
    expected=sp.simplify((-omega*sp.sin(k*x-omega*T)*psi
                        +sp.sqrt(1+t*t)*m*z*z*sp.besselj(1,m*z))/t**2)
    assert sp.simplify(required_source-expected)==0
    residual=sp.simplify(required_source.subs({t:1,z:1,T:0,x:0,k:1,m:1}))
    assert sp.simplify(residual-sp.sqrt(2)*sp.besselj(1,1))==0
    return dict(exact_bulk_TT_PDE=True, original_moving_normal=True,
                boundary_source_equals_exact_normal_trace=True,
                selected_nonzero_source=float(residual.evalf(16)),
                prescribed_israel_stress_normalization=False,
                source_is_nonlocal_separated_wave=True,
                retarded_zero_initial_data=False,
                finite_energy_tensor=False, graviton_receiver=False)

def audit():
    return {'cylinder':cylinder_audit(),'ads5':ads_tensor_audit(),
            'status':'partial closures only: compact finite-energy scalar; exact sourced TT boundary trace, not physical graviton retarded propagator'}
if __name__=='__main__':
    print(json.dumps(audit(),indent=2,sort_keys=True))
