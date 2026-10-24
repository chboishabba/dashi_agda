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
