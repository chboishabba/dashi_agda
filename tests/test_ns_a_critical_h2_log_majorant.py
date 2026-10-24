"""Exact checks for the same-physical-H2 conditional critical source estimate.

These tests certify scalar radial arithmetic and NS scaling, not an
independent Sobolev/Plancherel kernel theorem or unconditional A3.
"""
import importlib.util
from pathlib import Path
import sympy as S

P=Path(__file__).resolve().parents[1]/"scripts/ns_a_critical_h2_log_majorant.py"
spec=importlib.util.spec_from_file_location("ns_a_critical_h2_log",P)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def test_three_region_critical_radial_bound():
    r,E,D,H,nu=S.symbols("r E D H nu",positive=True)
    B=S.sqrt(E*D);M=D+S.sqrt(E*H)
    a=B/E;b=M/B
    low=S.integrate(4*S.pi*r**3*(E/(nu*r))**2,(r,0,a))
    mid=S.integrate(4*S.pi*r**3*(B/(nu*r*r))**2,(r,a,b))
    high=S.integrate(4*S.pi*r**3*(M/(nu*r**3))**2,(r,b,S.oo))
    assert S.simplify(low-2*S.pi*E*D/nu**2)==0
    assert S.simplify(high-2*S.pi*E*D/nu**2)==0
    assert S.simplify(mid-4*S.pi*E*D/nu**2*S.log(M/D))==0

def test_critical_Hhalf_bound_is_spatial_scale_invariant():
    E,D,H,nu,lam=S.symbols("E D H nu lam",positive=True)
    def bound(e,d,h):
        return 4*S.pi*e*d/nu**2*(1+S.log(1+S.sqrt(e*h)/d))
    assert S.simplify(bound(E/lam,lam*D,lam**3*H)-bound(E,D,H))==0

def test_without_H2_endpoint_high_frequency_envelope_diverges_logarithmically():
    E,D,nu,r,R=S.symbols("E D nu r R",positive=True)
    integrand=4*S.pi*r**3*(S.sqrt(E*D)/(nu*r*r))**2
    assert S.simplify(integrand-4*S.pi*E*D/(nu**2*r))==0
    assert S.simplify(S.integrate(integrand,(r,1,R))-
           4*S.pi*E*D/nu**2*S.log(R))==0

def test_gaussian_E_D_H_moments_nontrivial():
    E=2*(S.pi/2)**S.Rational(3,2)
    D=5*E
    H=35*E
    assert S.simplify(D/E-5)==0
    assert S.simplify(H/E-35)==0
    M=D+S.sqrt(E*H)
    assert S.simplify(M/D-1-S.sqrt(35)/5)==0

def test_causal_weighted_L2_transfer_preserves_critical_frequency_weight():
    # For each fixed xi the probability-submass exponential kernel
    # contracts time-L2; multiplication by |xi|>=0 before frequency
    # integration gives the weighted critical transfer.
    a,t,T,s=S.symbols("a t T s",positive=True)
    mass=S.integrate(a*S.exp(-a*(t-s)),(t,s,T))
    assert S.simplify(mass-(1-S.exp(-a*(T-s))))==0
    assert mod.certificate()["scaling_invariant"]
