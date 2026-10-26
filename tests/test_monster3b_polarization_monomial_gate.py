#!/usr/bin/env python3
"""Synthetic GF3 controls; NOT AtlasRep source-word verification."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_polarization_monomial_gate as g

def fixture(h=6):
    n=2*h
    I=[[int(i==j) for j in range(n)] for i in range(n)]
    L=[[int(i==j) for j in range(h)] for i in range(n)]
    F=[[0]*n for _ in range(n)]
    J=[[0]*n for _ in range(n)]
    for j in range(h):
        F[j][h+j]=2
        F[h+j][j]=1
        J[j][h+j]=1
        J[h+j][j]=2
    return I,L,F,J

def test_identity_preserves_polarization():
    I,L,_,J=fixture()
    r=g.check(I,L,J)
    assert r["span_original_and_transformed_rank"]==6
    assert r["simple_basis_permutation_not_ruled_out"]
    assert not r["monomial_action_sufficiently_proved"]

def test_quarterturn_fourier_exchange_needs_mixing():
    _,L,F,J=fixture()
    r=g.check(F,L,J)
    assert r["span_original_and_transformed_rank"]==12
    assert r["fourier_Weil_mixing_required_if_nonpreserving"]

def test_deficient_lagrangian_fails_closed():
    I,L,_,J=fixture()
    L[0]=L[1][:]
    try:g.check(I,L,J)
    except ValueError:pass
    else:raise AssertionError("deficient Lagrangian was accepted")

def test_centre_inverting_antisymplectic_can_still_preserve():
    I,L,_,J=fixture()
    for i in range(6,12):I[i][i]=2
    r=g.check(I,L,J)
    assert r["symplectic_multiplier"]==2
    assert r["preserves_chosen_polarization"]

def test_bad_form_and_not_similitude_rejected():
    I,L,_,J=fixture()
    bad=[row[:] for row in J]
    bad[0][0]=1
    try:g.check(I,L,bad)
    except ValueError:pass
    else:raise AssertionError("nonalternating form accepted")
    singular=[row[:] for row in I]
    singular[0]=[0]*12
    try:g.check(singular,L,J)
    except ValueError:pass
    else:raise AssertionError("nonsimilitude accepted")
