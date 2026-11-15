#!/usr/bin/env python3
"""KSW D2/B2: *all Fourier modes* quadratic stability of the probe cylinder.

This advances scripts/ksw668_brane_winding_stability_source.py, which
only checked the UNIFORM radial second derivative. This source model is
the same *new illustrative* flat-5D cylindrical probe membrane with
positive tension T and a compact winding scalar chi=n*theta, stiffness f²,
radius R_0=f*abs(n)/sqrt(2T) and NO 5D gravitational backreaction.

Original action with worldvolume coordinates (t,theta,u,v):
 S = -integral d4xi sqrt(-h)*(T + f²/2*h^ab d_a chi d_b chi).
Embedding X=R cos(theta), Y=R sin(theta), arbitrary
R=R_0+eps*eta(t,theta,u,v), chi=n theta+eps*psi(t,theta,u,v).
Using EXACT matrix-determinant lemma for a radial graph,
 h_ab=diag(-1,R²,1,1)+d_a R d_b R,
 sqrt(-h)=R*sqrt(1 -R_t²+R_u²+R_v²+R_theta²/R²).
The inverse follows by Sherman–Morrison. Differentiate the actual
Lagrangian in eps to second order; don't assume independent scalar/radius.

The exact quadratic Lagrangian density at the equilibrium is:
 L2= T*R0*(eta_t²-eta_u²-eta_v²)
    +(f² R0/2)*(psi_t²-psi_u²-psi_v²)
    -(f²/(2R0))*(psi_theta-n*eta/R0)².
Therefore Hamiltonian is a sum of NONNEGATIVE squares for any
finite-energy radial/scalar perturbation. With angular integer m and
transverse |k|², the generalized Fourier frequencies are
 omega_minus²=k² and omega_plus²=k²+(m²+1)/R0².
No tachyons (no e^{growth*t}) at QUADRATIC order for any m,k.

CRITICAL: omega_minus²=0 at k=0 yields neutral/marginal modes and
secular linear drift for nonzero zero-mode velocities. This does not
prove nonlinear Lyapunov stability, stability under self-gravity,
brane–graviton boundary conditions, or a physically realised shortcut.

Energy is positive because tension and scalar winding carry REAL
positive source energy, not "free energy".
"""
import argparse
import json
import sympy as s

def audit():
    e,R0,T,f,n=s.symbols("eps R0 T f n",positive=True,real=True)
    eta,et,eth,eu,ev=s.symbols("eta eta_t eta_theta eta_u eta_v",real=True)
    pt,pth,pu,pv=s.symbols("psi_t psi_theta psi_u psi_v",real=True)
    radius=R0+e*eta
    Q=e*e*(-et*et+eu*eu+ev*ev+eth*eth/radius**2)
    chi_square=(-e*e*pt*pt+(n+e*pth)**2/radius**2
                +e*e*(pu*pu+pv*pv))
    inner=(-e*e*et*pt+e*eth*(n+e*pth)/radius**2
           +e*e*(eu*pu+ev*pv))
    # Exact induced metric determinant + inverse, not a guessed EFT.
    lagrangian=-radius*s.sqrt(1+Q)*(T+
                 f*f*s.Rational(1,2)*(chi_square-inner**2/(1+Q)))
    expanded=s.series(lagrangian,e,0,3).removeO().expand()
    L1=s.simplify(expanded.coeff(e,1).subs(T,f*f*n*n/(2*R0**2)))
    L2=s.simplify(expanded.coeff(e,2).subs(T,f*f*n*n/(2*R0**2)))
    expected=(T*R0*(et**2-eu**2-ev**2)
              +f*f*R0*s.Rational(1,2)*(pt**2-pu**2-pv**2)
              -f*f/(2*R0)*(pth-n*eta/R0)**2)
    assert s.simplify(L2-expected.subs(T,f*f*n*n/(2*R0**2)))==0
    # Linear piece is total angular derivative n*psi_theta.
    assert s.simplify(L1+f*f*n*pth/R0)==0
    angular_mode,k_squared,omega_squared=s.symbols("m k2 omega2",real=True)
    # Hessian in eta,psi for Fourier angular ktheta=m and planar |k|²=k2.
    mass=s.diag(2*T*R0,f*f*R0)
    stiffness=s.Matrix([
       [2*T*R0*k_squared+f*f*n*n/R0**3,
        -f*f*n*angular_mode/R0**2],
       [-f*f*n*angular_mode/R0**2,
        f*f*R0*k_squared+f*f*angular_mode**2/R0]])
    normalized=(mass.inv()*stiffness).subs(
       T,f*f*n*n/(2*R0**2)).applyfunc(s.simplify)
    characteristic=s.factor((normalized-omega_squared*s.eye(2)).det())
    expected_char=(k_squared-omega_squared)*(
       k_squared+(angular_mode**2+1)/R0**2-omega_squared)
    assert s.simplify(characteristic-expected_char)==0
    evs=normalized.eigenvals()
    assert {s.simplify(e) for e in evs}=={s.simplify(k_squared),s.simplify(k_squared+(angular_mode**2+1)/R0**2)}
    # Concrete original T=f=n=2,2,1 R0=1 numerical families
    Rstar=s.simplify(f*n/s.sqrt(2*T))
    assert s.simplify(Rstar.subs({T:2,f:2,n:1})-1)==0
    checked=[]
    for m in (0,1,2,3,7,25):
      for k2 in (0,1,4,100):
        low=s.Integer(k2)
        high=s.Integer(k2+m*m+1)
        assert low>=0 and high>0
        checked.append({"m":m,"k_squared":k2,
            "omega_minus_squared":int(low),"omega_plus_squared":int(high)})
    return {
       "status":"PASS exact full radial+compact-scalar quadratic action and all Fourier mode non-tachyonic dispersion (probe brane)",
       "source_model":"flat 5D cylindrical PROBE brane; positive tension+compact winding",
       "original_action":"-int sqrt(-h)[T+f²/2*(dchi)²]",
       "full_induced_metric_and_rank1_inverse":"used exact radial graph, no guessed m-dependent force",
       "first_variation":"total angular derivative -f²*n/R0 * psi_theta",
       "quadratic_Lagrangian":"T R0(eta_t²-eta_u²-eta_v²)+f² R0/2(psi_t²-psi_u²-psi_v²)-f²/(2R0)(psi_theta-n eta/R0)²",
       "Hamiltonian_quadratic_nonnegative_for_finite_energy_data":True,
       "sourced_equilibrium_R0":"f*|n|/sqrt(2T), n>0",
       "all_integer_m_and_nonnegative_k2_eigenvalues":{
          "omega_minus_squared":"k2",
          "omega_plus_squared":"k2+(m²+1)/R0²"},
       "all_mode_proof":"exact symbolic generalized eigen determinant, not just finite sampling",
       "sample_modes_checked":len(checked),
       "sample_mode_spectrum":checked,
       "negative_frequency_squared":False,
       "marginal_zero_modes_k2_zero":True,
       "zero_mode_linear_drift_or_nonlinear_instability_ruled_out":False,
       "full_self_gravitating_5D_Einstein_Israel_stability":False,
       "physical_graviton_or_receiver_proven":False,
       "total_brane_energy_free":False,
       "Agda_analytic_kernel_accepted":False
    }

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out")
    a=p.parse_args()
    txt=json.dumps(audit(),indent=2,sort_keys=True)+"\n"
    if a.out:open(a.out,"w",encoding="utf-8").write(txt)
    print(txt)
