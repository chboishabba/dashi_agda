#!/usr/bin/env python3
"""Build a source-bounded DRMD reconstruction manifest from arXiv:2602.23895 Table I.

This script intentionally does not claim to recover the authors' original MCMC manifest.
The sampled z_stop coordinate is reconstructed from the published best-fit log10(z_dec)
using the paper's approximate Eq. (13) with (G/H)_ini fixed to 1e7.
"""

import json
import math

PAPER_ARXIV = "2602.23895"
LOG10_ZDEC_BEST_FIT = 3.350
G_OVER_AH_INI = 1.0e7


def build_manifest() -> dict:
    z_dec = 10.0 ** LOG10_ZDEC_BEST_FIT
    z_stop = (1.0 + z_dec) * math.log(G_OVER_AH_INI) - 1.0

    return {
        "manifest_kind": "paper-table-reconstruction",
        "source": {
            "arxiv": PAPER_ARXIV,
            "table": "Table I",
            "analysis": "DRMD + SH0ES-calibrated SN",
        },
        "parameters": {
            "omega_b": 0.02318,
            "omega_cdm": 0.1382,
            "H0": 72.50,
            "ln10^10A_s": 3.051,
            "n_s": 0.9798,
            "tau_reio": 0.0581,
            "delta_Neff_drmd": 0.87,
            "f_idm_drmd": 0.039,
            "log10_z_dec_published": LOG10_ZDEC_BEST_FIT,
            "z_dec_reconstructed_from_log10": z_dec,
            "G_over_aH_drmd_ini": G_OVER_AH_INI,
            "z_stop_reconstructed_eq13": z_stop,
            "N_ncdm": 1,
            "m_ncdm_eV": 0.06,
            "T_ncdm_over_T_gamma": 0.716,
            "alpha_s": 0.0,
            "beta_s": 0.0,
        },
        "published_derived_coordinates": {
            "r_d_BAO_Mpc_over_h": 100.0,
            "r_d_DAO_Mpc_over_h": 58.6,
            "A_DAO": 0.036,
        },
        "provenance": {
            "original_mcmc_manifest_recovered": False,
            "equation13_approximation_used": True,
            "z_stop_directly_published": False,
            "large_scale_structure_data_used_for_this_table_column": False,
            "safe_label": "source-bounded paper-table reconstruction",
        },
    }


def main() -> None:
    print(json.dumps(build_manifest(), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
