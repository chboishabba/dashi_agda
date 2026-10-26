#!/usr/bin/env python3
"""Synthetic SU3 Wilson-line spectrum / Hosotani selection diagnostic.

Original: Y. Hosotani, Ann Phys 190 (1989) 233;
DOI 10.1016/0003-4916(89)90015-8. Also his PRD69 (2004) 125014.
No such selection mechanism on a horned wild complement is derived.
DASHI donor: NeutrinoHornedSU3RootExact and SUNWilsonClassFunction.

Prototype: a VECTORLIKE 3-component particle on an ordinary smooth
circle L=1 with a flat SU3 holonomy W. Covariant Laplacian eigenvalues
(2*pi*n+theta_j)^2, theta_j eigenphases of W.
Heat trace is sum exp(-t lambda_nj). This is gauge-invariant
spectral algebra, NOT a prediction about measured leptons or horns.
The ordinary circle counterexample means this result is NOT wild-
topology-specific. A one-loop effective potential would additionally
require regularized matter determinants, statistics and boundary
conditions; it is NOT calculated here.
"""
from math import pi,sqrt
import numpy as np

D=181846007130841
def fixture():
    z=np.exp(2j*pi/3)
    s12,c12=161/289,240/289
    s13,c13=240/1609,1591/1609
    s23,c23=20/29,21/29
    U=np.array([
        [c12*c13,s12*c13,s13*np.conj(z)],
        [-s12*c23-c12*s23*s13*z,c12*c23-s12*s23*s13*z,s23*c13],
        [s12*s23-c12*c23*s13*z,-c12*s23-s12*c23*s13*z,c23*c13]
    ],dtype=complex)
    T=np.diag([1,z,z*z])
    return T@(2*np.outer(U[:,0],np.conj(U[:,0]))-np.eye(3))
def heat_trace(phases,t,levels=18):
    n=np.arange(-levels,levels+1)
    return float(sum(np.sum(np.exp(-t*(2*pi*n+th)**2)) for th in phases))
def compute():
    W=fixture()
    phases=np.sort(np.angle(np.linalg.eigvals(W)))
    zero=np.zeros(3)
    assert abs(sum(phases))<1e-10
    assert np.linalg.norm(W@W.conj().T-np.eye(3))<1e-11
    assert abs(np.linalg.det(W)-1)<1e-11
    expected_trace=complex((176093404722400+19836986431118/2)/D,
                            -(19836986431118/D)*sqrt(3)/2)
    assert abs(np.trace(W)-expected_trace)<2e-12
    for t in (.025,.1,.2,.5,1):
        val=heat_trace(phases,t)
        trivial=heat_trace(zero,t)
        print("t",t,"heat(W)",val,"heat(identity)",trivial,"difference",val-trivial)
    assert abs(heat_trace(phases,.2)-2.2535171069536086)<1e-10
    assert abs(heat_trace(zero,.2)-3.002234083836318)<1e-10
    # Trace class on compact circle for any fixed t>0. This says
    # NOTHING about uniform trace-class bounds on shrinking wild ends.
    spectral_gap=min(abs(2*pi*n+th) for n in (-1,0,1) for th in phases)
    assert abs(spectral_gap-.09593953432280523)<1e-9
    print("eigenphases",phases,"gap",spectral_gap)
    print("GOTO/HATCHER geometric source selection: NOT ESTABLISHED")
    print("FULL RENORMALIZED HOSOTANI POTENTIAL: NOT CALCULATED")
    return phases
if __name__=="__main__":
    compute()
