"""Fail-closed R734 witness vs R369 sampled finite-to-tail Gram operator.

A signed core-core physical transfer must not be relabeled the sampled
positive-part phase/triad pair-incidence cross block at K=N-1, N>=6.
"""
from itertools import product
from sympy import pi, cos, simplify, Max
from test_ns_r734_pure_plus_physical_w2_no_go import P,Q,K,minus,critical_data

MODES=[P,Q,K,minus(P),minus(Q),minus(K)]
def radius(m):return max(map(abs,m))
def add(m,n):return tuple(a+b for a,b in zip(m,n))

def test_original_witness_and_its_quadratic_image_are_below_sampled_gram_tail():
    assert max(map(radius,MODES))==2
    sums=[add(p,q) for p,q in product(MODES,repeat=2)]
    assert max(map(radius,sums))==4
    for N in (6,8,10,12):
        cutoff=N-1
        assert all(radius(m)<=cutoff for m in MODES)
        assert all(radius(m)<=cutoff for m in sums)
        # The restricted cross-block on this witness at t=0 has no
        # sampled tail support. This does not constrain the global
        # K_N(A) operator spectrum or later-time new modes.

def test_dyadic_production_remains_nonzero_inside_all_sampled_core_sets():
    assert simplify(critical_data()[2]>0)==True
    assert radius(K)==2

def test_phase_positive_truncation_is_not_the_signed_transfer_map():
    # The scripted pair-incidence uses max(cos(phi_i+phi_j-phi_l),0).
    assert Max(cos(0),0)==1
    assert Max(cos(pi),0)==0
    assert cos(0)==-cos(pi)
    # This only tests information loss under truncation. It does not
    # identify scripted pi_i,phi_i with this physical Fourier datum.
