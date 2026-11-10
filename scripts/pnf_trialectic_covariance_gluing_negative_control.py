#!/usr/bin/env python3
"""Exact local-vs-global covariance gluing counterexample.

The three overlapping 2x2 financial/PNF correlation charts can each be
strictly PSD, and agree on the diagonal overlaps, while the global 3x3
correlation matrix is indefinite. This is a *mathematical negative control*,
not observed economics or an assertion about the psychology of trialectics.

Source reuses DASHI's 3-chart trialectic gluing and pants seam separation.
"""
from fractions import Fraction as Q
import json

def pair_psd(rho):
    # 2x2 correlation [[1,rho],[rho,1]] positive definiteness
    return 1-rho*rho > 0

def all_three_pairs_local_valid(rho):
    return all(pair_psd(rho) for _ in range(3))

def global_ones_quadratic(rho):
    # (1,1,1)^T C (1,1,1), with all three cross-correlations rho
    return Q(3)+Q(6)*rho

def exact_gluing_obstruction():
    rho = -Q(3,4)
    bad = {
        "rho": str(rho),
        "chart_AB_determinant": str(1-rho*rho),
        "chart_BC_determinant": str(1-rho*rho),
        "chart_CA_determinant": str(1-rho*rho),
        "all_local_pair_charts_PD": all_three_pairs_local_valid(rho),
        "all_diagonal_overlaps_identical": True,
        "global_ones_quadratic": str(global_ones_quadratic(rho)),
        "global_PSD": False,
        "global_negative_eigenvalue": str(1+2*rho),
        "two_other_global_eigenvalues": str(1-rho),
        "interpretation": "local covariance charts compatible but global PSD requires joint cross-chart condition",
    }
    assert all_three_pairs_local_valid(rho)
    assert 1-rho*rho == Q(7,16)
    assert global_ones_quadratic(rho) == -Q(3,2)
    assert 1+2*rho == -Q(1,2)
    assert 1-rho == Q(7,4)
    return bad

def tests():
    for rho in [Q(0),Q(1,4),-Q(1,4)]:
        assert all_three_pairs_local_valid(rho)
        assert global_ones_quadratic(rho) >= 0
    assert exact_gluing_obstruction()["global_PSD"] is False
    return "PASS: exact local-PD/global-indefinite gluing negative control"

if __name__ == "__main__":
    print(tests())
    print(json.dumps(exact_gluing_obstruction(),indent=2))
