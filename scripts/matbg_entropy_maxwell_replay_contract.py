#!/usr/bin/env python3
"""Source-faithful Maxwell entropy replay kernel for Zhang et al. 2026.

Implements Eqs. (10)-(12) in the paper:
  (∂S/∂ν)_T = -(∂μ/∂T)_ν
  S(ν,T) = -∫_4^ν (∂μ/∂T)_ν dν
and the numerically preferred equivalent
  S(ν,T) = -∂_T ∫_4^ν μ(ν,T) dν.

The paper estimates the derivative from three adjacent temperature points.
This producer validates that algorithm on a synthetic analytic fixture only.
No experimental XLSX values are used and no measured entropy replay is claimed.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import numpy as np

SOURCE_DOI = "10.1038/s41467-026-76179-y"
NU = np.array([0., 1., 2., 3., 4.])
TEMPERATURES_K = np.array([10., 20., 30.])

def integrate_from_full_filling(mu_row):
    # np.trapezoid integrates from ν to 4; negate to obtain ∫_4^ν.
    return np.array([
        -float(np.trapezoid(mu_row[j:], NU[j:]))
        for j in range(len(NU))
    ])

def three_point_entropy(mu_grid):
    integrated = np.array([integrate_from_full_filling(row) for row in mu_grid])
    entropies = []
    for j in range(len(NU)):
        slope = float(np.polyfit(TEMPERATURES_K, integrated[:, j], 1)[0])
        entropies.append(-slope)
    return integrated, np.array(entropies)

def main():
    # Analytic fixture μ(ν,T)=a(ν)T with a(ν)=10^-3(4-ν) meV/K.
    mu = np.array([
        [0.001 * (4.0 - nu) * T for nu in NU]
        for T in TEMPERATURES_K
    ])
    integrated, entropy = three_point_entropy(mu)

    # Analytic S(ν)= -∫_4^ν a(ν')dν' = 0.0005(4-ν)^2 meV/K.
    expected = np.array([0.0005 * (4.0 - nu) ** 2 for nu in NU])
    max_error = float(np.max(np.abs(entropy - expected)))

    assert max_error < 1e-14
    assert abs(entropy[-1]) < 1e-14
    assert abs(entropy[0] - 0.008) < 1e-14

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/matbg_entropy_maxwell_replay_contract.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "source_doi": SOURCE_DOI,
        "source_equations": {
            "maxwell": "dS/dnu = -dmu/dT",
            "boundary": "S(nu=4,T)=0",
            "preferred_order": "S(nu,T) = -d/dT integral_4^nu mu(nu,T) dnu",
            "temperature_derivative": "linear fit over three adjacent temperature points",
        },
        "fixture": {
            "nu": NU.tolist(),
            "temperatures_K": TEMPERATURES_K.tolist(),
            "mu_meV": mu.tolist(),
        },
        "integral_4_to_nu_mu_meV": integrated.tolist(),
        "entropy_meV_per_K": entropy.tolist(),
        "expected_entropy_meV_per_K": expected.tolist(),
        "max_abs_error": max_error,
        "assertions_passed": True,
        "promotion_boundaries": {
            "experimental_xlsx_used": False,
            "measured_entropy_replay": False,
            "same_sample_qtm_entropy": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
