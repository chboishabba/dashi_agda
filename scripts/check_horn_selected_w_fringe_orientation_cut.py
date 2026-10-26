#!/usr/bin/env python3
"""Exact selected SU3 Wilson two-arm ORIENTATION discriminator.

Prior owners: source-selected cyclotomic W and chosen unpolarized
two-path interferometer belong to neutrino Agda PR #1247
(NeutrinoHornedWilsonInterferenceExact.agda). Hatcher, Algebraic
Topology Ex 2B.2 supplies the original source-marked commutator
tower. Horn owner #1244 owns C3 spatial action/basing paths.
Agda #1249 / Lean #84 own the orientation-robust operator-norm
selected-W obstruction.

This new receiver-facing CONSUMER preserves that attribution:
conjugating W leaves tr(W) and ALL fringes unchanged, but
inverting loop orientation sends tr(W)->conj(tr(W)) and
P_{W^-1}(phi)=P_W(-phi). At phi=0 the original exact port probability
is unchanged; the calibrated ODD-IN-PHASE component changes sign.
No C3 novelty or lepton physics is manufactured from that sign.

The analytic phase convention requires independent direction/phase
calibration in any actual apparatus. Arbitrarily swapping input arms
or control-phase conventions can also flip the sign. There is no
same-source Hatcher physical loop, detector, or phase dataset here.
"""
from fractions import Fraction as F
from math import sqrt

D = 181846007130841
A = F(176093404722400, D)
B = F(19836986431118, D)     # tr W = A - B*zeta3
real_trace = A + B / 2         # zeta3 = -1/2 + i sqrt(3)/2
imag_trace_sq = F(3,4) * B*B
P0 = F(1,2) + real_trace/6
odd_fringe_sq = B*B/12

assert B>0
assert P0 == F(434928608401, 648677790003)
assert odd_fringe_sq == F(98376507667089911639682481,
                          99203910928289627462680101843)
assert imag_trace_sq > 0
print("PASS original exact source P(phi=0) invariant under W inversion",P0)
print("PASS exact squared signed phase contrast (P(+pi/2)-P(-pi/2))²",
      odd_fringe_sq, "contrast magnitude",sqrt(float(odd_fringe_sq)))

try:
    import numpy as np
    from math import pi
    z = np.exp(2j*pi/3)
    s12,c12=161/289,240/289
    s13,c13=240/1609,1591/1609
    s23,c23=20/29,21/29
    U=np.array([
        [c12*c13,s12*c13,s13*np.conj(z)],
        [-s12*c23-c12*s23*s13*z,c12*c23-s12*s23*s13*z,s23*c13],
        [s12*s23-c12*c23*s13*z,-c12*s23-s12*c23*s13*z,c23*c13]
    ],dtype=complex)
    W=np.diag([1,z,z*z])@(2*np.outer(U[:,0],np.conj(U[:,0]))-np.eye(3))
    Wrev=W.conj().T
    G=np.diag((1,z,z*z))
    P=lambda X,phi: .5 + np.real(np.exp(1j*phi)*np.trace(X))/6
    for phi in (0,.3,pi/2,pi):
        assert abs(P(Wrev,phi)-P(W,-phi)) < 1e-12
        assert abs(P(G@W@G.conj().T,phi)-P(W,phi)) < 1e-12
    contrast=P(W,pi/2)-P(W,-pi/2)
    assert abs(contrast**2-float(odd_fringe_sq)) < 1e-12
    assert contrast>0
    assert P(Wrev,pi/2)-P(Wrev,-pi/2)<0
    assert abs(P(W,0)-float(P0))<1e-12
    assert abs(np.linalg.norm(W-np.eye(3),2)-
               np.linalg.norm(Wrev-np.eye(3),2))<1e-12
    print("PASS original same W/W^-1 fringe, four phases, conjugation and norm")

    # Curved selected-source eta is the operator norm difference
    # between the ACTUAL based parent Wilson matrix U and ACTUAL
    # transported child commutator V. Common whisker/orientation
    # changes of BOTH do not affect eta; changing only one can.
    V = G@W@G.conj().T
    eta = np.linalg.norm(W-V,ord=2)
    eta_inv = np.linalg.norm(W.conj().T-V.conj().T,ord=2)
    eta_conj = np.linalg.norm(
        G@W@G.conj().T-G@V@G.conj().T,ord=2)
    assert eta>1e-5
    assert abs(eta_inv-eta)<1e-12
    assert abs(eta_conj-eta)<1e-12
    # FAIL-CLOSED if ONLY root is rebased: for V=G W G*, the
    # one-sided apparent defect becomes zero although eta>0.
    assert np.linalg.norm(G@W@G.conj().T-V,ord=2)<1e-12
    print("PASS paired SU3 eta inversion/common conjugation; one-sided gauge-basing false positive caught")
except ImportError:
    print("SKIP optional numpy exact-original-matrix controls")

# Fail-closed: an UNCALIBRATED source arm-phase convention is not
# independent experimental evidence of the orientation-odd sign.
print("OPEN orientation calibration, actual Hatcher loop, live interferometer")
