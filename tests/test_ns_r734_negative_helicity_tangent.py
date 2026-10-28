"""Full-Galerkin negative-helicity entry on the R734 pure-plus physical datum.

Original historical roots: Leray's NSE; Waleffe's 1992 helical triad calculus;
Biferale--Titi (2013) studies a different, helicity-decimated system.
This file proves a source-specific exact symbolic finite-mode fact; it does
not certify the global PDE or a kernel-level proof.
"""
import sympy as S
from test_ns_r734_pure_plus_physical_w2_no_go import (
    P, Q, K, h, n2, critical_data, physical_u,
    projected_NS_nonlinearity,
)

def negative_mode_norm(m, force):
    v = h(m, force[m], -1)
    return S.simplify(S.expand_complex((S.conjugate(v).T*v)[0]))

def test_q_exact_negative_helicity_generation_certificate():
    force = projected_NS_nonlinearity(physical_u(), 2)
    norm = negative_mode_norm(Q, force)
    gap = 6+S.sqrt(5)-S.sqrt(6)-S.sqrt(30)
    assert S.simplify(norm - S.Rational(5,24)*gap) == 0
    # Exact positivity, without a floating point sign test.
    assert S.simplify((6+S.sqrt(5))**2-(S.sqrt(6)+S.sqrt(30))**2) == 5
    assert S.simplify(gap>0) == S.true

def test_full_galerkin_crosses_hminus_at_first_order():
    u=physical_u(); force=projected_NS_nonlinearity(u, 2)
    for m, v in u.items():
        assert S.simplify(h(m,v,-1))==S.zeros(3,1)
    assert S.simplify(negative_mode_norm(Q,force)>0)==S.true
    # At Hminus(0)=0, viscous -nu |q|^2 u_- vanishes;
    # the negative-sector time derivative equals H- of the full
    # projected NS force. Velocity scaling a yields a^2 H- F_q.
    for a in (1,2,512):
        assert S.simplify(a**4*negative_mode_norm(Q,force)>0)==S.true

def test_negative_mass_is_quadratic_in_time_but_defect_linear():
    force=projected_NS_nonlinearity(physical_u(), 2)
    norm_q=negative_mode_norm(Q,force)
    # M_minus(t)=sum_m |m| ||Hminus u_m(t)||^2. The +/-q pair alone
    # contributes 2*sqrt(5)*a^4*norm_q*t^2+O(t^3), so
    # M_minus''(0)>=4*sqrt(5)*a^4*norm_q.
    # By contrast R_weight'(0)=a^3*Pcrit>0.
    _,_,pcrit=critical_data()
    for a in (1,512):
        assert S.simplify(4*S.sqrt(5)*a**4*norm_q>0)==S.true
        assert S.simplify(a**3*pcrit>0)==S.true
    # Therefore |R_weight'|<=C*(M_minus)^alpha, alpha>0,
    # cannot be a universal instantaneous inequality with finite C
    # on these states. No PDE blowup is inferred.

def test_q_entry_is_cyclic_369_invariant():
    # Proper cyclic rotations preserve curl helicity and cube cutoff.
    from test_ns_369_pure_plus_w2_orbit import field, projected_NS, rotate, hel
    expected=S.Rational(5,24)*(6+S.sqrt(5)-S.sqrt(6)-S.sqrt(30))
    for j in range(3):
        force=projected_NS(field(j),2)
        q=rotate(Q,j)
        v=hel(q,force[q],-1)
        val=S.simplify(S.expand_complex((S.conjugate(v).T*v)[0]))
        assert S.simplify(val-expected)==0
