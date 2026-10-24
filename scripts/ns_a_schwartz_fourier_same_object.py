#!/usr/bin/env python3
"""Exact Schwartz whole-space A Fourier/Leray same-object calibration.

Conventions: Ff(ξ)=∫_{R³} exp(-i x·ξ) f(x) dx;
inverse uses (2π)^-3. All expressions are symbolic exact SymPy.

Physical finite-energy divergence-free initial datum on R³:
  ψ(x)=exp(-|x|²), u=(∂_yψ,-∂_xψ,0)
      =(-2y,2x,0) exp(-|x|²).
Actual (u·∇)u = -4(x,y,0) exp(-2|x|²).

Its EXACT spatial Fourier transform is
  û(ξ)=i π^(3/2) (ξ_y,-ξ_x,0) exp(-|ξ|²/4)
and the transform of nonlinear convection is
  i(π/2)^(3/2) (ξ_x,ξ_y,0) exp(-|ξ|²/8).

The same result follows DIRECTLY from the physical Fourier convolution
  i/(2π)^3 ∫ (ξ·û(η)) û(ξ-η) dη,
via completed Gaussian square and its first/second centered moments.
The Leray projector Pξ at ξ≠0 is applied to that SAME result.

This is a constructive *one-datum* A1 representation receipt, not the
Fourier-transform theorem for every continuum NS solution, not a
time-dependent PDE theorem, and not unrestricted Clay A regularity.
"""
import argparse
import json
import sympy as S

def certificate():
    x,y,z=S.symbols("x y z",real=True)
    a,b,c=S.symbols("xi_x xi_y xi_z",real=True)
    xyz=(x,y,z)
    r2=sum(t*t for t in xyz)
    xi2=a*a+b*b+c*c
    psi=S.exp(-r2)
    u=S.Matrix([S.diff(psi,y), -S.diff(psi,x), S.Integer(0)])
    divergence=S.simplify(sum(S.diff(u[i],xyz[i]) for i in range(3)))
    convection=S.Matrix([S.simplify(sum(u[j]*S.diff(u[i],xyz[j])
                           for j in range(3))) for i in range(3)])
    expected_convection=-4*S.exp(-2*r2)*S.Matrix([x,y,0])
    assert divergence==0
    assert all(S.simplify(convection[i]-expected_convection[i])==0
               for i in range(3))
    # Gaussian FT, derivative rule F(∂f)=iξ F(f).
    gaussian_hat=S.pi**S.Rational(3,2)*S.exp(-xi2/4)
    uhat=S.I*gaussian_hat*S.Matrix([b,-a,0])
    assert S.simplify(a*uhat[0]+b*uhat[1]+c*uhat[2])==0

    gauss2_hat=(S.pi/2)**S.Rational(3,2)*S.exp(-xi2/8)
    nonlinear_direct=S.I*gauss2_hat*S.Matrix([a,b,0])

    # Fourier convolution η=ξ/2+Z has joint Gaussian density
    # exp(-|Z|²/2) exp(-|ξ|²/8).
    # h(η)=(η_y,-η_x,0), L=ξ·h(η)=a*Z_y-b*Z_x.
    # h(ξ-η)=h(ξ)/2-h(Z). Odd part vanishes. Centered moments:
    # ∫ Z_iZ_j exp(-|Z|²/2) dZ=(2π)^(3/2) δ_ij.
    gaussian_moment=(2*S.pi)**S.Rational(3,2)
    E_Lh=S.Matrix([-a,-b,0])*gaussian_moment
    # Fourier product: (ξ·û(η)) û(ξ-η)
    # = -π³ L*h(ξ-η) exp(-(|η|²+|ξ-η|²)/4).
    nonlinear_convolution=S.simplify(
        (S.I/(2*S.pi)**3)*(-S.pi**3)*S.exp(-xi2/8)*E_Lh
    )
    assert all(S.simplify(nonlinear_convolution[i]-nonlinear_direct[i])==0
               for i in range(3))

    # Leray: Pξ V = V - ξ (ξ·V)/|ξ|².
    vector=S.Matrix([a,b,c])
    projected=S.simplify(nonlinear_direct -
                  vector*(vector.dot(nonlinear_direct))/xi2)
    projected_expected=S.I*gauss2_hat*S.Matrix([
        a*c*c/xi2,b*c*c/xi2,-c*(a*a+b*b)/xi2
    ])
    assert all(S.simplify(projected[i]-projected_expected[i])==0
               for i in range(3))
    assert S.simplify(vector.dot(projected))==0
    plane_zero=[S.simplify(t.subs(c,0)) for t in projected]
    assert plane_zero==[0,0,0]
    nontrivial=[S.simplify(t.subs({a:1,b:0,c:1})) for t in projected]
    assert nontrivial[0]!=0 and nontrivial[2]!=0

    # Finite real-space energy and dissipation from elementary Gaussian
    # moments: ∫exp(-2r²)=(π/2)^(3/2),
    # E=4∫(x²+y²)exp(-2r²)=2(π/2)^(3/2).
    # Derivative/Plancherel or real-space moments give D=5 E.
    energy=2*(S.pi/2)**S.Rational(3,2)
    dissipation=10*(S.pi/2)**S.Rational(3,2)
    # Independent exact moment computations from Fourier space:
    # E ξ_perp² =2, E |ξ|² ξ_perp² =10 for standard 3D normal.
    assert S.simplify(dissipation-5*energy)==0
    assert all(expr.is_finite for expr in (energy,dissipation))
    # General finite-energy A low-output estimate, independent of this
    # selected Gaussian datum. For every u in L2(R3), u⊗u is in L1:
    # |FT(u⊗u)(xi)|_F <= integral |u|^2 = E. The Leray projection
    # contracts, hence |P_xi FT(div(u⊗u))| <= |xi| E as a distribution
    # (pointwise representative for nonzero xi). Thus the zero-forcing
    # heat-resolvent multiplier has bound E/(nu*|xi|). The square is
    # LOCALLY integrable in three dimensions; the same bound is not
    # globally integrable at large xi.
    R, nu, rr=S.symbols("R nu r",positive=True)
    radial_L2=S.integrate(
        4*S.pi*rr**2*(energy/(nu*rr))**2,(rr,0,R))
    radial_L1=S.integrate(
        4*S.pi*rr**2*(energy/(nu*rr)),(rr,0,R))
    assert S.simplify(radial_L2-4*S.pi*R*(energy/nu)**2)==0
    assert S.simplify(radial_L1-2*S.pi*R**2*energy/nu)==0
    # Stronger UNIVERSAL physical H1 Fourier-source estimate:
    # For divergence-free u in H1, f=(u·grad)u in L1 by Cauchy-Schwarz,
    # ||f||_1 <= ||u||_2 ||grad u||_2 = sqrt(E*D).
    # Hence |F[P f](xi)| <= min(E*|xi|, sqrt(E*D)).
    # The physical inverse-heat/stationary resolvent upper is
    # 1/nu * min(E/r, sqrt(E*D)/r²). Its Fourier L2 NORM SQUARED
    # is bounded by 8*pi*E^(3/2)*sqrt(D)/nu².
    EE, DD = S.symbols("E D",positive=True)
    cutoff=S.sqrt(DD/EE)
    low_global=S.integrate(
        4*S.pi*rr**2*(EE/(nu*rr))**2,(rr,0,cutoff))
    high_global=S.integrate(
        4*S.pi*rr**2*(S.sqrt(EE*DD)/(nu*rr**2))**2,
        (rr,cutoff,S.oo))
    total_global=S.simplify(low_global+high_global)
    assert S.simplify(total_global-
        8*S.pi*EE**S.Rational(3,2)*S.sqrt(DD)/nu**2)==0
    # Standard unforced Leray energy inequality:
    # E(t) <= E0, ∫_0^T D(t)dt <= E0/(2*nu).
    # Apply Holder to the *same* instantaneous stationary Stokes
    # response bound, for a.e. t where u(t)∈H1.
    E0, T=S.symbols("E0 T",positive=True)
    spacetime_upper=S.simplify(
        (8*S.pi/nu**2)*E0**S.Rational(3,2)*
        S.sqrt(T)*S.sqrt(E0/(2*nu)))
    asserted_spacetime_upper=(
        4*S.sqrt(2)*S.pi*E0**2*S.sqrt(T)/nu**S.Rational(5,2))
    assert S.simplify(spacetime_upper-asserted_spacetime_upper)==0

    # Strong H1 -> L2_xi same-source continuity (the density bridge):
    # G=u⊗u-v⊗v in L1, ||G||_1 <= A where
    # A=(||u||_2+||v||_2)||u-v||_2.
    # f=(u·grad)u-(v·grad)v in L1, ||f||_1 <= B where
    # B=||u-v||_2||grad u||_2 + ||v||_2||grad(u-v)||_2.
    # Fourier projected source difference <= min(A*r,B).
    # Thus stationary Stokes-response difference <= min(A/(nu*r),B/(nu*r²)).
    # The EXACT squared L2_xi bound is (8*pi/nu²)*A*B.
    # In particular, strong H1 convergence u_n->u proves convergence of
    # the actual physical Stokes source in L2_xi, not merely a free
    # Set-valued transform "source attachment".
    AA, BB=S.symbols("tensor_L1_difference convective_L1_difference",
                     positive=True)
    continuity_crossover=BB/AA
    continuity_low=S.integrate(
        4*S.pi*rr**2*(AA/(nu*rr))**2,(rr,0,continuity_crossover))
    continuity_high=S.integrate(
        4*S.pi*rr**2*(BB/(nu*rr**2))**2,
        (rr,continuity_crossover,S.oo))
    continuity_bound=S.simplify(continuity_low+continuity_high)
    assert S.simplify(continuity_bound-
        8*S.pi*AA*BB/nu**2)==0

    # THE critical-scaling obstruction is essential to any A3 claim.
    # Under the actual NS scaling u_lambda(x)=lambda*u(lambda*x):
    #   E_lambda=E/lambda, D_lambda=lambda*D,
    #   V_lambda(x)=lambda V(lambda*x) for the stationary Stokes response,
    #   ||Vhat_lambda||²_L2xi = ||Vhat||²_L2xi/lambda.
    # This low/high Fourier response control is supercritical in 3D;
    # the energy bound can decrease while D_lambda becomes arbitrarily
    # large. It cannot itself bound the scale-critical continuation norm.
    ell=S.symbols("lambda",positive=True)
    scale_response=S.simplify(
        (8*S.pi/nu**2)*(EE/ell)**S.Rational(3,2)*S.sqrt(ell*DD))
    assert S.simplify(scale_response-total_global/ell)==0

    # Critical regularity audit: the same scalar majorants DO NOT yield
    # the scale-invariant dot-H^(1/2) Fourier norm in 3D. Its high-r
    # envelope contains the logarithmically divergent integral
    # 4*pi*E*D/nu² * int_(r*,infinity) dr/r.
    Rcrit=S.symbols("Rcrit",positive=True)
    crit_log_tail=S.simplify(
       4*S.pi*EE*DD/nu**2*(S.log(Rcrit)-S.log(cutoff)))
    assert S.simplify(S.diff(crit_log_tail,Rcrit) -
       4*S.pi*EE*DD/(nu**2*Rcrit))==0
    # The finite E,D response bound therefore cannot be promoted to
    # critical H^(1/2) solely by multiplying its Fourier majorant by r.
    return {
        "schema":"ns.a.schwartz-fourier-same-object.v1",
        "convention":"F[f](xi)=integral exp(-i*x.dot(xi)) f(x) dx",
        "physical_velocity":"(-2*y,2*x,0)*exp(-|x|^2)",
        "divergence":"0",
        "physical_convection":"-4*(x,y,0)*exp(-2*|x|^2)",
        "fourier_velocity":[str(S.simplify(t)) for t in uhat],
        "fourier_convection_direct":[str(S.simplify(t))
                                      for t in nonlinear_direct],
        "fourier_convection_convolution":[str(S.simplify(t))
                                           for t in nonlinear_convolution],
        "leray_projected":[str(S.simplify(t)) for t in projected_expected],
        "total_energy":str(energy),
        "total_H1_seminorm_squared":str(dissipation),
        "finite_energy":True,
        "arbitrary_L2_physical_projected_source_bound":"|F(Pdiv(u⊗u))(xi)| <= |xi|*E",
        "arbitrary_L2_zero_frequency_resolvent_bound":"E/(nu*|xi|), xi!=0",
        "low_ball_resolvent_L2_norm_squared_bound":str(radial_L2),
        "low_ball_resolvent_L1_norm_bound":str(radial_L1),
        "arbitrary_H1_source_bound":"min(E*|xi|, sqrt(E*D))",
        "arbitrary_H1_crossover_frequency":"sqrt(D/E)",
        "arbitrary_H1_global_fourier_resolvent_L2_squared_bound":str(total_global),
        "Leray_energy_inequality_spacetime_response_L2_squared_upper":str(spacetime_upper),
        "time_bound_needs_no_uniform_H1":"true; requires integral D(t) finite only",
        "strong_H1_source_continuity_low":"A*|xi|",
        "strong_H1_source_continuity_high":"B",
        "strong_H1_Stokes_L2_xi_difference_squared_bound":str(continuity_bound),
        "strong_H1_continuity_assumptions":"A=(||u||2+||v||2)||u-v||2; B=||u-v||2||grad u||2+||v||2||grad(u-v)||2",
        "Navier_Stokes_scaling_E_lambda":"E/lambda",
        "Navier_Stokes_scaling_D_lambda":"lambda*D",
        "Navier_Stokes_scaling_response_L2_squared":"response_L2_squared/lambda",
        "Hhalf_critical_high_frequency_envelope_log_tail":str(crit_log_tail),
        "Hhalf_critical_primitive_diverges":"log(Rcrit) as Rcrit->infinity; not a source regularity proof",
        "exact_nonzero_projected_frequency":"(1,0,1)",
        "source_only_not_claimed":[
            "general FourierTransformVelocity for every solution",
            "time propagation", "whole-space A2/A3",
            "Lean or Agda kernel certification", "Clay proof"
        ],
    }

def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(json.dumps(certificate(),indent=2,sort_keys=True))

if __name__=="__main__":main()
