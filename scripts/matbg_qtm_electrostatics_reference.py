#!/usr/bin/env python3
"""Numerical QTM three-plate electrostatics reference.

Uses Xiao et al. Nature 653 (2026), DOI 10.1038/s41586-026-10378-x:
  -e V_b = mu_B - mu_T - e^2 n_T / C_g
   e V_bg = mu_B + e^2 (n_B+n_T) / C_bg
with experimentally calibrated C_bg=62.3 nF cm^-2 and C_g=2.3 uF cm^-2.

The fixture sets mu_B=mu_T=0, V_b=10 mV and V_bg=10 V to isolate the
pure capacitor conversion. It is not a replay of the paper's measured skew
map and does not infer chemical potentials from experimental data.
"""

from __future__ import annotations
import hashlib
import json
from pathlib import Path

E_C = 1.602176634e-19
CBG_F_CM2 = 62.3e-9
CG_F_CM2 = 2.3e-6
VB_V = 0.010
VBG_V = 10.0
MU_B_EV = 0.0
MU_T_EV = 0.0

# With chemical potentials set to zero, the source equations reduce to
# n_T = C_g V_b / e and n_B+n_T = C_bg V_bg / e.
n_t_cm2 = CG_F_CM2 * VB_V / E_C
n_total_cm2 = CBG_F_CM2 * VBG_V / E_C
n_b_cm2 = n_total_cm2 - n_t_cm2

assert n_t_cm2 > 0.0
assert n_total_cm2 > n_t_cm2
assert abs((n_b_cm2 + n_t_cm2) - n_total_cm2) / n_total_cm2 < 1e-15

script_path = Path(__file__)
receipt = {
    "script": "scripts/matbg_qtm_electrostatics_reference.py",
    "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
    "source_doi": "10.1038/s41586-026-10378-x",
    "fixture": {
        "V_b_V": VB_V,
        "V_bg_V": VBG_V,
        "mu_B_eV": MU_B_EV,
        "mu_T_eV": MU_T_EV,
        "C_bg_F_cm2": CBG_F_CM2,
        "C_g_F_cm2": CG_F_CM2,
    },
    "results": {
        "n_T_cm^-2": n_t_cm2,
        "n_B_plus_n_T_cm^-2": n_total_cm2,
        "n_B_cm^-2": n_b_cm2,
        "tip_density_per_bias_volt_cm^-2_V^-1": CG_F_CM2 / E_C,
        "total_density_per_backgate_volt_cm^-2_V^-1": CBG_F_CM2 / E_C,
    },
    "assertions_passed": True,
    "promotion_boundaries": {
        "measured_skew_map_replayed": False,
        "chemical_potential_inversion": False,
        "qtm_data_fit": False,
        "same_sample_entropy": False,
        "agda_kernel_receipt": False,
    },
}

print(json.dumps(receipt, indent=2, sort_keys=True))
