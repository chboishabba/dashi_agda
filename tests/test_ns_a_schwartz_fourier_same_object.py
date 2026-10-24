"""Exact Schwartz Fourier convolution/Leray calibration of the whole-space A carrier."""
import importlib.util
from pathlib import Path
import sympy as S

SCRIPT=Path(__file__).resolve().parents[1]/"scripts/ns_a_schwartz_fourier_same_object.py"
SPEC=importlib.util.spec_from_file_location("ns_a_schwartz",SCRIPT)
module=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(module)

def test_exact_real_spatial_and_fourier_same_object():
    data=module.certificate()
    assert data["divergence"]=="0"
    assert data["fourier_convection_direct"]==data["fourier_convection_convolution"]
    assert data["finite_energy"]
    assert len(data["leray_projected"])==3

def test_physical_schwartz_energy_and_nonlinear_leray_are_nontrivial():
    x,y,z,a,b,c=S.symbols("x y z xi_x xi_y xi_z",real=True)
    r2=x*x+y*y+z*z
    psi=S.exp(-r2)
    u=S.Matrix([S.diff(psi,y),-S.diff(psi,x),0])
    expected=-4*S.Matrix([x,y,0])*S.exp(-2*r2)
    computed=S.Matrix([S.simplify(sum(u[j]*S.diff(u[i],(x,y,z)[j])
                   for j in range(3))) for i in range(3)])
    assert all(S.simplify(computed[i]-expected[i])==0 for i in range(3))
    norm2=a*a+b*b+c*c
    F=S.I*(S.pi/2)**S.Rational(3,2)*S.exp(-norm2/8)
    projected=F*S.Matrix([
        a*c*c/norm2,b*c*c/norm2,-c*(a*a+b*b)/norm2
    ])
    assert S.simplify(S.Matrix([a,b,c]).dot(projected))==0
    assert S.simplify(projected[0].subs({a:1,b:0,c:1}))!=0

def test_no_global_regulariy_or_unjustified_transform_claim():
    data=module.certificate()
    not_claimed=" ".join(data["source_only_not_claimed"])
    assert "every solution" in not_claimed
    assert "time propagation" in not_claimed
    assert "kernel certification" in not_claimed


def test_arbitrary_finite_energy_low_frequency_response_is_locally_L2():
    # Analytical theorem: u in L2 -> u⊗u in L1; each Fourier
    # component of the physical tensor is bounded by E=||u||_2².
    # P_xi has norm ≤1 and divergence supplies one |xi| factor:
    # |P_xi F[div(u⊗u)]| ≤ E |xi|.
    # Dividing by the actual positive heat rate nu|xi|² gives
    # E/(nu|xi|), whose SQUARED R3 integral over B_R is finite.
    R,nu,E,r=S.symbols("R nu E r",positive=True)
    upper=E/(nu*r)
    ball_l2=S.integrate(4*S.pi*r*r*upper*upper,(r,0,R))
    ball_l1=S.integrate(4*S.pi*r*r*upper,(r,0,R))
    assert S.simplify(ball_l2-4*S.pi*R*E**2/nu**2)==0
    assert S.simplify(ball_l1-2*S.pi*R*R*E/nu)==0

    receipt=module.certificate()
    assert receipt["arbitrary_L2_physical_projected_source_bound"] == (
        "|F(Pdiv(u⊗u))(xi)| <= |xi|*E")
    assert "R" in receipt["low_ball_resolvent_L2_norm_squared_bound"]
    assert "R" in receipt["low_ball_resolvent_L1_norm_bound"]


def test_real_finite_H1_source_has_global_L2_heat_inverse_majorant():
    # u∈H1, div u=0:
    # |F[P(u·grad u)]|<=min(E*r,sqrt(E*D)).
    # Divide by nu*r²: low E/(nu*r), high sqrt(E*D)/(nu*r²).
    E,D,nu,r=S.symbols("E D nu r",positive=True)
    rt=S.sqrt(D/E)
    low=S.integrate(4*S.pi*r*r*(E/(nu*r))**2,(r,0,rt))
    high=S.integrate(4*S.pi*r*r*(S.sqrt(E*D)/(nu*r*r))**2,
                     (r,rt,S.oo))
    expected=8*S.pi*E**S.Rational(3,2)*S.sqrt(D)/nu**2
    assert S.simplify(low+high-expected)==0
    receipt=module.certificate()
    assert receipt["arbitrary_H1_source_bound"]=="min(E*|xi|, sqrt(E*D))"
    assert "sqrt(D/E)"==receipt["arbitrary_H1_crossover_frequency"]
    assert "D" in receipt["arbitrary_H1_global_fourier_resolvent_L2_squared_bound"]


def test_leray_energy_gives_finite_T_spacetime_source_response():
    E0,T,nu=S.symbols("E0 T nu",positive=True)
    # ||StokesInverse F_nonlin(t)||²_(L2_xi)
    # <= (8pi/nu²) E(t)^(3/2) sqrt(D(t)).
    # E(t)<=E0 and ∫_0^T D(t) <= E0/(2nu).
    via_holder=(8*S.pi/nu**2)*E0**S.Rational(3,2)*(
        S.sqrt(T)*S.sqrt(E0/(2*nu)))
    expected=4*S.sqrt(2)*S.pi*E0**2*S.sqrt(T)/nu**S.Rational(5,2)
    assert S.simplify(via_holder-expected)==0
    assert ("sqrt(T)" in module.certificate()[
        "Leray_energy_inequality_spacetime_response_L2_squared_upper"])


def test_strong_H1_density_same_source_stokes_continuity():
    # Two fields u,v: A controls L1(u⊗u-v⊗v), B controls the L1
    # difference of (u·grad)u and (v·grad)v. The Leray/Stokes
    # Fourier response then has low A/(nu*r), high B/(nu*r²).
    A,B,nu,r=S.symbols("A B nu r",positive=True)
    rc=B/A
    low=S.integrate(4*S.pi*r*r*(A/(nu*r))**2,(r,0,rc))
    high=S.integrate(4*S.pi*r*r*(B/(nu*r*r))**2,(r,rc,S.oo))
    assert S.simplify(low+high-8*S.pi*A*B/nu**2)==0
    report=module.certificate()
    assert report["strong_H1_source_continuity_low"]=="A*|xi|"
    assert report["strong_H1_source_continuity_high"]=="B"
    assert ("tensor_L1_difference" in
            report["strong_H1_Stokes_L2_xi_difference_squared_bound"])
    assert ("convective_L1_difference" in
            report["strong_H1_Stokes_L2_xi_difference_squared_bound"])


def test_ns_scaling_prevents_mistaking_direct_stokes_bound_for_A3():
    # Genuine NS symmetry u_lambda=lambda*u(lambda*x,lambda²*t).
    # For a spatial slice E_lambda=E/lambda, D_lambda=lambda*D;
    # the Stokes response V_lambda=lambda*V(lambda*x) and its
    # Fourier L2 norm squared scales like 1/lambda, while
    # D_lambda becomes arbitrarily large at small spatial scales.
    E,D,nu,lam=S.symbols("E D nu lam",positive=True)
    base=(8*S.pi/nu**2)*E**S.Rational(3,2)*S.sqrt(D)
    scaled=(8*S.pi/nu**2)*(E/lam)**S.Rational(3,2)*S.sqrt(lam*D)
    assert S.simplify(scaled-base/lam)==0
    result=module.certificate()
    assert result["Navier_Stokes_scaling_E_lambda"]=="E/lambda"
    assert result["Navier_Stokes_scaling_D_lambda"]=="lambda*D"
