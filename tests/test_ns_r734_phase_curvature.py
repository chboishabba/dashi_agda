"""Exact Waleffe-transfer spectral-weight curvature and phase-blind no-go.

Same R734 physical six-mode cutoff, not a different shell surrogate. Historical
triad energy/helicity invariant belongs to Waleffe (1992); this is a
DASHI-source-specific exact algebraic/regression certificate, not Clay A/B.
"""
import sympy as S
from test_ns_r734_pure_plus_physical_w2_no_go import (
    P,Q,K,h,n2,minus,physical_u,projected_NS_nonlinearity,critical_data
)
A=(5-S.sqrt(5)+S.sqrt(30))/10
r0=S.Integer(1);r1=S.sqrt(5);r2=S.sqrt(6)
T=(r1-r2,r2-r0,r0-r1)

def pair_transfers(u):
    f=projected_NS_nonlinearity(u,2)
    return tuple(S.simplify(S.expand_complex(
        4*S.re((S.conjugate(u[m]).T*f[m])[0]))) for m in (P,Q,K))

def test_triads_weighted_production_is_secant_slope_drop():
    w0,w1,w2=S.symbols('w0 w1 w2', real=True)
    p=A*(T[0]*w0+T[1]*w1+T[2]*w2)
    curvature=A*(r1-r0)*(r2-r1)*(
        (w1-w0)/(r1-r0)-(w2-w1)/(r2-r1))
    assert S.simplify(p-curvature)==0

def test_energy_and_true_helicity_affine_radial_weights_cancel():
    x,y=S.symbols('x y',real=True)
    weighted=S.expand(sum((x+y*r)*t for r,t in zip((r0,r1,r2),T)))
    assert S.simplify(weighted)==0
    assert S.simplify(sum(T))==0
    assert S.simplify(sum(r*t for r,t in zip((r0,r1,r2),T)))==0
    # On this nondegenerate triad these are the only weight triples
    # with zero transfer for both signs of the common triadic phase.
    w0,w1=S.symbols('w0 w1',real=True)
    w2=S.solve(T[0]*w0+T[1]*w1+T[2]*S.Symbol('w2'),S.Symbol('w2'))[0]
    assert S.simplify(w2-(w1+(r2-r1)*(w1-w0)/(r1-r0)))==0

def test_original_dyadic_weight_is_strict_downward_slope_jump():
    assert S.simplify((S.Integer(2)-1)/(r1-r0)>0)==S.true
    assert S.simplify((S.Integer(2)-2)/(r2-r1))==0
    critical=S.simplify(A*(T[0]+2*T[1]+2*T[2]))
    assert S.simplify(critical-A*(r2-r1))==0
    assert S.simplify(critical-critical_data()[2])==0
    assert S.simplify(critical>0)==S.true

def test_actual_physical_phase_flip_reverses_source_transfer_without_energy_change():
    u=physical_u()
    v={m:(-z if m in (K,minus(K)) else z) for m,z in u.items()}
    for m,z in v.items():
        assert S.simplify(h(m,z,-1))==S.zeros(3,1)
        assert S.simplify((S.conjugate(z).T*z)[0]-(S.conjugate(u[m]).T*u[m])[0])==0
    tt=pair_transfers(u); ttf=pair_transfers(v)
    assert all(S.simplify(t-A*pred)==0 for t,pred in zip(tt,T))
    assert all(S.simplify(t+tflip)==0 for t,tflip in zip(tt,ttf))
    p=S.simplify(tt[0]+2*tt[1]+2*tt[2]);pf=S.simplify(ttf[0]+2*ttf[1]+2*ttf[2])
    assert S.simplify(p+pf)==0
    assert S.simplify(p>0)==S.true and S.simplify(pf<0)==S.true
    # Same spectra and ternary wave-vector signs, opposite signed transfer.
    # Consequently those phase-blind data cannot uniquely determine Pcrit.
