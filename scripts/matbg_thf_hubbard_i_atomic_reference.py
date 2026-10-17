#!/usr/bin/env python3
"""Source-bounded atomic Hubbard-I reference for the 2026 MATBG THF model.

Uses Xiao et al. Nature 653 (2026) source parameters U=60 meV, N=8,
tau^-1=1 meV. This is the non-hybridized f-electron propagator at the
particle-hole-symmetric reference delta_mu=0. It is not the paper's full
self-consistent c-f solution and is not a QTM data fit.
"""

import json
import math
from pathlib import Path

U_MEV = 60.0
N = 8.0
GAMMA_MEV = 1.0
DELTA_MU_MEV = 0.0

def weights(nu_f):
    return 0.5 + nu_f / N, 0.5 - nu_f / N

def spectral_function(omega_mev, nu_f):
    lower, upper = weights(nu_f)
    x_lower = omega_mev + DELTA_MU_MEV + U_MEV / 2.0
    x_upper = omega_mev + DELTA_MU_MEV - U_MEV / 2.0
    return (
        lower * GAMMA_MEV / math.pi / (x_lower * x_lower + GAMMA_MEV**2)
        + upper * GAMMA_MEV / math.pi / (x_upper * x_upper + GAMMA_MEV**2)
    )

rows = []
for nu_f in range(-4, 5):
    lower, upper = weights(nu_f)
    rows.append(
        {
            "nu_f": nu_f,
            "lower_hubbard_weight": lower,
            "upper_hubbard_weight": upper,
            "weight_sum": lower + upper,
            "A_minus_30_meV": spectral_function(-30.0, nu_f),
            "A_plus_30_meV": spectral_function(+30.0, nu_f),
        }
    )

assert all(abs(row["weight_sum"] - 1.0) < 1e-15 for row in rows)
assert rows[4]["lower_hubbard_weight"] == rows[4]["upper_hubbard_weight"] == 0.5
assert rows[0]["lower_hubbard_weight"] == 0.0 and rows[0]["upper_hubbard_weight"] == 1.0
assert rows[-1]["lower_hubbard_weight"] == 1.0 and rows[-1]["upper_hubbard_weight"] == 0.0

evidence = {
    "model": "Xiao-2026 non-hybridized f-electron Hubbard-I atomic reference",
    "source_doi": "10.1038/s41586-026-10378-x",
    "parameters": {
        "U_meV": U_MEV,
        "N": int(N),
        "tau_inverse_meV": GAMMA_MEV,
        "delta_mu_meV_fixture": DELTA_MU_MEV,
    },
    "pole_centres_meV": [-30.0, 30.0],
    "fillings": rows,
    "assertions_passed": True,
    "promotion_boundaries": {
        "full_c_f_hybridization": False,
        "self_consistent_density_and_mu": False,
        "qtm_data_fit": False,
        "same_sample_entropy": False,
        "agda_kernel_receipt": False,
    },
}

print(json.dumps(evidence, indent=2, sort_keys=True))
