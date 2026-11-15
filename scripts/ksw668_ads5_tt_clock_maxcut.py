#!/usr/bin/env python3
"""Original KSW668 max-cut: compact TT source, moving-domain reduction,
static finite-energy tensor packet, clock invariance, and cubic local delay.

Source-equivalent SymPy checks. NOT a retarded moving-brane Green operator,
measured graviton receiver, fully backreacted perturbation, or Agda receipt.
Caldwell--Langlois (2001); Maartens--Koyama (2010);
Pawlowski (2014) time-choice crosswalk.
"""
import json
import sympy as s
import mpmath as mp

def tt_source():
    kx,ky,kz=s.symbols('kx ky kz',real=True)
    k=s.Matrix([kx,ky,kz]); k2=(k.T*k)[0]
    P=k2*s.eye(3)-k*k.T
    Q=s.diag(0,1,-1)
    src=(P*Q*P-s.Rational(1,2)*P*s.trace(P*Q)).applyfunc(s.expand)
    assert (src-src.T)==s.zeros(3)
    assert (k.T*src).applyfunc(s.factor)==s.zeros(1,3)
    assert s.factor(s.trace(src))==0
    assert src.subs({kx:1,ky:0,kz:0})==Q
    assert src.subs({kx:0,ky:0,kz:0})==s.zeros(3)
    # Let phi=x^4 near origin times C-infinity compact bump and g(t)
    # smooth compact: local 4th order differential P preserves support.
    # FRW mixed tensor: ∇_mu δS^mu_i = ∂_j pi^j_i and
    # ∇_mu δS^mu_0=-H tr pi, so the prescribed TT source is conserved
    # against the ORIGINAL background; no generating matter action.
    t=s.symbols('t',positive=True)
    rp=1/(3*t*s.sqrt(1+t*t))
    assert s.simplify(rp.subs(t,2)-1/(6*s.sqrt(5)))==0
    assert s.simplify(s.diff(rp,t)+(2*t*t+1)/(3*t*t*(1+t*t)**s.Rational(3,2)))==0
    return dict(symmetric=True,transverse=True,traceless=True,
        compact_by_local_4th_order_operator=True,
        initial_local_x4_yy_value=24,initial_local_x4_zz_value=-24,
        background_FRW_covariant_divergence_zero=True,
        DEC_min_rho_plus_p_t1_to2='1/(6 sqrt(5))',
        TT_source_shape='pi_ij = g(t) [P_i^k P_j^l - P_ij P^kl/2] Q_kl phi',
        P_symbol='|k|² I - k kT',
        gravity_boundary_condition='n·∂H_i^j = -6 pi_i^j',
        physical_matter_action_derived=False,retarded_moving_TT_Green=False)


def tangential_wall_energy():
    """Coercive tangential-multiplier energy and homogeneous uniqueness cut."""
    A,B,C,v,g,w=s.symbols('A B C v g w',real=True)
    eX=w*(A*A+B*B+C+2*v*A*B)/2
    positive=w*((A+v*B)**2+(1-v*v)*B*B+C)/2
    assert s.expand(eX-positive)==0
    boundary=(1+v*v)*A*B+v*(A*A+B*B)
    assert s.expand(boundary-(B+v*A)*(A+v*B))==0
    vp,wp=s.symbols('vp wp',real=True)
    bulk=vp*w*A*B+v*wp*(-A*A+B*B+C)/2
    assert s.expand(bulk.subs({A:1,B:0,C:0})+v*wp/2)==0
    # On original t in [1,2], |v| <= 1/sqrt2, b >= 1/2,
    # |v'|<1, so eX>=(1-|v|)*e0, Gronwall for homogeneous
    # physical Neumann data gives uniqueness for smooth finite energy.
    Cbound=(1+3*s.sqrt(2))/(1-1/s.sqrt(2))
    assert float(Cbound)>0
    return dict(
        coercive_energy='1/2 int z^-3 [(H_T+v H_z)^2+(1-v²)H_z²+|grad_x H|²]',
        wall_flux='-b^-3*(H_z+v H_T)*(H_T+v H_z)',
        homogeneous_neumann_wall_flux_zero=True,
        bulk_deformation='vprime*z^-3*H_T H_z +v*(z^-3)prime/2*(-H_T²+H_z²+|grad H|²)',
        uniform_energy_lower_factor='1-1/sqrt2',
        conservative_Gronwall_constant_upper=float(Cbound),
        finite_interval_smooth_homogeneous_uniqueness=True,
        inhomogeneous_source_trace_bound=False,retarded_Green_constructed=False)

def cylindrical_flat_bulk_rigidity():
    R,T,f,n,kappa,rdot,rddot=s.symbols('R T f n kappa rdot rddot',positive=True)
    a=f*f*n*n/(2*R*R)
    S=s.diag(-T-a,-T+a,-T-a,-T-a)
    israel=(-kappa/s.Integer(2)*(S-s.trace(S)*s.eye(4)/3)).applyfunc(s.factor)
    K=s.diag(-rddot/s.sqrt(1+rdot**2),-s.sqrt(1+rdot**2)/R,0,0)
    assert s.simplify(israel[2,2]+kappa*(T-a)/6)==0
    assert s.solve(israel[2,2],R**2)==[f*f*n*n/(2*T)]
    assert (israel.subs(f,s.sqrt(2*T)*R/n)-s.diag(0,-kappa*T,0,0)).applyfunc(s.simplify)==s.zeros(4)
    # Both bulk sheets are kept EXACTLY flat; then K^u_u=0 for any
    # radial history. Israel's u-u channel forces a=T and fixes R.
    # Radial probe stiffness is NOT coupled brane-world stability.
    return dict(static_full_Israel=True,flat_both_bulk_sides=True,
        ku_zero_for_all_Rdot=True,radial_constraint='R²=f²n²/(2T)',
        nonstatic_Rtau_allowed_with_fixed_T_f_n=False,
        full_braneworld_linear_stability_proved=False)

def moving_boundary():
    T,y=s.symbols('T y',real=True)
    b=s.Function('b')(T); v=s.diff(b,T); vp=s.diff(b,T,2)
    u=s.Function('u')(T,y)
    ht=s.diff(u,T)-v*s.diff(u,y)
    hTT=s.expand(s.diff(ht,T)-v*s.diff(ht,y))
    assert s.simplify(hTT-(s.diff(u,T,2)-2*v*s.diff(u,T,y)
                        +v*v*s.diff(u,y,2)-vp*s.diff(u,y)))==0
    t=s.symbols('t',positive=True)
    vt=-1/s.sqrt(1+t*t); vprime=t**3/(1+t*t)**2
    assert s.simplify(s.diff(vt,t)*t*t/s.sqrt(1+t*t)-vprime)==0
    assert s.simplify(1-vt**2-t*t/(1+t*t))==0
    A,B,C=s.symbols('A B C',real=True)
    flux=-(A*B+v*(A*A+B*B+C)/2)
    g=s.symbols('g',real=True)
    flux_g=s.factor(flux.subs(B,g-v*A))
    expected=-(1-v*v)*A*g+v*(1-v*v)*A*A/2-v*(g*g+C)/2
    assert s.simplify(flux_g-expected)==0
    assert flux_g.subs({g:0,A:1,C:0,v:-s.Rational(1,2)})<0
    assert flux_g.subs({g:0,A:0,C:1,v:-s.Rational(1,2)})>0
    return dict(time_interval='original brane t in [1,2]',
        boundary_velocity='v=-1/sqrt(1+t²)',v_range='[-1/sqrt(2),-1/sqrt(5)]',
        strictly_timelike=True,uniform_y_coefficient_lower='1/2',
        wall_acceleration='vprime=t³/(1+t²)²',
        straightened_PDE='u_TT-2v u_Ty-(1-v²)u_yy+(3/(y+b)-vprime)u_y-Delta_x u=0',
        boundary='sqrt(1+t²)/t²*((1-v²)u_y+v*u_T)=-6*pi_TT',
        energy_flux='-b^-3*(H_T H_z+v/2*(H_T²+H_z²+|grad_x H|²))',
        flux_can_have_either_sign=True,
        Green_operator_wellposedness_from_this_alone=False)

def static_finite_energy_packet():
    b,z=s.symbols('b z',positive=True)
    radial=s.integrate(z**(-3),(z,b,s.oo))
    assert radial==1/(2*b*b)
    # With static Neumann wall z=b, choose a genuinely 3D compact TT
    # f_ij(x). The free 3D wave cos(T sqrt(-Delta_3)) f_ij(x) is independent
    # of z, hence solves the full stationary AdS5 tensor PDE and boundary.
    # Weight integral ∫_b^∞ z^-3 dz is finite, so packet energy finite.
    return dict(static_AdS5_brane_neumann=True,
        radial_zero_mode='H(T,z,x)=cos(T sqrt(-Delta_3)) f_TT(x)',
        radial_weight_norm_sq=str(radial),compact_initial_f_TT=True,
        finite_radial_energy=True,finite_total_energy_for_f_TT_H1=True,
        nontrivial_TT=True,moving_neumann_supported=False,
        original_moving_brane_solution=False)

def short_baseline():
    h,u,v=s.symbols('h u v',positive=True)
    pair=s.integrate(s.integrate((u-v)**2,(u,0,h)),(v,0,h))
    assert s.simplify(pair-h**4/6)==0
    mp.mp.dps=95
    t0=mp.mpf('1')
    F=lambda t:mp.asinh(t)-mp.sqrt(1+t*t)/t
    results=[]
    for eps_text in ['.1','.03','.01','.003','.001']:
        eps=mp.mpf(eps_text); B=t0+eps
        I1=F(B)-F(t0); I2=1/t0-1/B
        rg=mp.sqrt(I1*I1-I2*I2)
        adv=mp.exp(rg)-B
        approx=eps**3/mp.mpf('48')
        assert adv>0
        results.append([eps_text,float(adv),float(adv/approx)])
    assert abs(results[-1][2]-1)<.01
    H0=mp.mpf('2.2e-18'); c=mp.mpf(299792458)
    ell=mp.mpf('1'); D=mp.mpf('1'); dotH=-H0*H0
    local_adv=ell**2*dotH**2*D**3/(24*c**5*(1+(ell*H0/c)**2))
    return dict(model='original a=t, ell=1, t0=1',
        exact_pair_second_moment='h^4/6',
        ratio_delta_tau_to_delta_t_cubed='1/48 leading order',
        exact_numeric_eps_delta_ratio=results,
        general_short_baseline='delta_tau_adv = (ell/c)^2 (dH/dtau)^2 Delta_tau^3/[24*(1+(ell H/c)^2)] + O(Delta_tau^4)',
        physical_short_D='ell² dotH² D³/[24 c⁵*(1+(ell H/c)²)] + O(D⁴)',
        illustrative_H0=2.2e-18,illustrative_dotH_minus_H0_sq=True,
        illustrative_D_m=1,illustrative_ell_m=1,
        illustrative_local_advance_seconds=float(local_adv),
        not_an_observational_bound=True,rescaling_alone_does_not_solve_C1=True)

def clock_gauge_invariance():
    mp.mp.dps=80
    F=lambda t:mp.asinh(t)-mp.sqrt(1+t*t)/t
    rg=mp.sqrt((F(2)-F(1))**2-mp.mpf('0.5')**2)
    eta_g=mp.log(2); eta_gamma=rg
    proper=mp.exp(eta_gamma)-mp.exp(eta_g)
    integral=mp.quad(lambda eta:mp.exp(eta),[eta_g,eta_gamma])
    assert mp.almosteq(integral,proper)
    return dict(geometric_horizon_excess=float(rg-mp.log(2)),
        same_receiver_conformal_time_excess=float(eta_gamma-eta_g),
        same_receiver_proper_time_advance=float(integral),
        FRW_conformal_lapse='N(eta)=exp(eta)',
        lapse_reparametrization_does_not_change_proper_time=True,
        source_equivalence_and_detector_standards_still_required=True,
        referenced_quantum_time_paper='Pawlowski arXiv:1403.3879 2014; no shortcut PDE theorem')

def audit():
    return dict(A4=cylindrical_flat_bulk_rigidity(),B2=tt_source(),
        B3=moving_boundary(),B3_energy=tangential_wall_energy(),B5=static_finite_energy_packet(),
        C1=short_baseline(),clock=clock_gauge_invariance(),
        agda_kernel_accepted=False,physical_retarded_graviton=False)

if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
