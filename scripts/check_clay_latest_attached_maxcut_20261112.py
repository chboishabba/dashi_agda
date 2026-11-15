#!/usr/bin/env python3
"""Additional source-adversarial Clay checks. Reference only, not a kernel proof."""
from fractions import Fraction as Q
from math import pi, exp, log, sin, cos, sqrt

def rh_local_curvature():
    for n in (3,7,19,100):
        eps=Q(1,n)
        assert -(eps*eps)/(eps**4) == -n*n
    assert -9 < -4

def rh_claimed_threshold():
    t=14.134725
    assert log(t/(2*pi))/(2*pi)-4 < 0
    T=2*pi*exp(8*pi)
    assert T > 10**11

def rh_first_mode_sign():
    g1,g2=Q(1),Q(2)
    mean=(g1*g1+g2*g2)/2
    assert mean == Q(5,2)
    assert g1**3*(g1*g1-mean) == -Q(3,2)
    f=lambda n: Q(1,2**n)-Q(4,4**n)
    assert f(1)<0<f(3)

def ns_periodic_internal_flux():
    # u=(sin y,sin x,0) is periodic, divergence free.
    # div((|u|²/2)u)=sin y sin x cos x + sin x sin y cos y.
    x=y=pi/4
    val=sin(y)*sin(x)*cos(x)+sin(x)*sin(y)*cos(y)
    assert abs(val-sqrt(2)/2)<1e-14 and val>0
    # A small internal box around this point has strictly positive flux.

def ns_bkm_requires_unpaid_integrability():
    # E(t)=(1-t)^(-1/2) obeys E'=E³/2, integral E = 2,
    # yet E becomes unbounded: not a Navier-Stokes flow.
    assert Q(1,2)<1<Q(3,2)
    for n in (10,100,1000):
        t=Q(n*n-1,n*n)
        assert t<1 and n*n*(1-t)==1

def ym_midpoint_precondition():
    # Unrestricted quadrature nodes: f(x)=x on [0,1],
    # f''=0 but endpoint sample f(0)=0 != integral 1/2.
    actual,endpoint,hess=Q(1,2),Q(0),Q(0)
    assert abs(actual-endpoint)>hess*Q(1,24)

def ym_shifted_denominator():
    q,p=pi,-pi
    assert abs(4*sin(q/2)**2-4)<1e-12
    assert 4*sin((q+p)/2)**2 == 0

def ym_modewise_not_uniform_gap():
    # H e_n=(1/(n+1)) e_n on l2, H Omega=0:
    # all eigenvalues positive and finite-support vectors dense,
    # but no uniform positive spectral lower bound.
    for m in (Q(1),Q(1,2),Q(2,3),Q(1,100),Q(3,19)):
        n=m.denominator
        assert 0<Q(1,n+1)<m

def ym_coupling_not_measure_convergence():
    # Same positive decreasing coupling 1/(n+1) can coexist with
    # alternating finite-state observables without any relation.
    for n in range(20):
        g=Q(1,n+1)
        assert g>0 and abs((n+1)%2-n%2)==1

if __name__=="__main__":
    tests=(rh_local_curvature,rh_claimed_threshold,rh_first_mode_sign,
           ns_periodic_internal_flux,ns_bkm_requires_unpaid_integrability,
           ym_midpoint_precondition,ym_shifted_denominator,
           ym_modewise_not_uniform_gap,ym_coupling_not_measure_convergence)
    for test in tests:
        test()
        print("PASS",test.__name__)
    print(f"{len(tests)}/{len(tests)} negative controls; zero Clay promotions")
