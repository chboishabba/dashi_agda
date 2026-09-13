#!/usr/bin/env python3
"""Build a source-bounded DRMD reconstruction manifest from arXiv:2602.23895 Table I.

This script intentionally does not claim to recover the authors' original MCMC manifest.
The sampled z_stop coordinate is reconstructed from the published best-fit log10(z_dec)
using the paper's approximate Eq. (13) with (G/H)_ini fixed to 1e7.
"""

import argparse
import json
import math

PAPER_ARXIV = "2602.23895"
LOG10_ZDEC_BEST_FIT = 3.350
G_OVER_AH_INI = 1.0e7


def build_manifest() -> dict:
    z_dec = 10.0 ** LOG10_ZDEC_BEST_FIT
    z_stop = (1.0 + z_dec) * math.log(G_OVER_AH_INI) - 1.0
    A_s = math.exp(3.051) * 1.0e-10

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
            "A_s": A_s,
            "ln10^10A_s_published": 3.051,
            "n_s": 0.9798,
            "tau_reio": 0.0581,
            "delta_Neff_drmd": 0.87,
            "f_idm_drmd": 0.039,
            "log10_z_dec_published": LOG10_ZDEC_BEST_FIT,
            "z_dec_reconstructed_from_log10": z_dec,
            "G_over_aH_drmd_ini": G_OVER_AH_INI,
            "z_stop_reconstructed_eq13": z_stop,
            "N_ur": 2.0308,
            "N_ncdm": 1,
            "m_ncdm": 0.06,
            "T_ncdm": 0.716,
            "YHe": "BBN",
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


def render_class_ini(manifest: dict) -> str:
    """Render only the source-bounded CLASS/DRMD parameter fragment.

    This is a reconstruction input fragment, not an authors' original chain/config file.
    """
    p = manifest["parameters"]
    lines = [
        f"# source: arXiv:{PAPER_ARXIV} Table I paper-table reconstruction",
        "# WARNING: z_stop is reconstructed with approximate Eq. (13); this is not the original MCMC manifest.",
        f"omega_b = {p['omega_b']}",
        f"omega_cdm = {p['omega_cdm']}",
        f"H0 = {p['H0']}",
        f"A_s = {p['A_s']:.17g}",
        f"n_s = {p['n_s']}",
        f"tau_reio = {p['tau_reio']}",
        f"delta_Neff_drmd = {p['delta_Neff_drmd']}",
        f"f_idm_drmd = {p['f_idm_drmd']}",
        f"z_stop = {p['z_stop_reconstructed_eq13']:.17g}",
        f"G_over_aH_drmd_ini = {p['G_over_aH_drmd_ini']:.17g}",
        f"N_ur = {p['N_ur']}",
        f"N_ncdm = {p['N_ncdm']}",
        f"m_ncdm = {p['m_ncdm']}",
        f"T_ncdm = {p['T_ncdm']}",
        f"YHe = {p['YHe']}",
        f"alpha_s = {p['alpha_s']}",
        f"beta_s = {p['beta_s']}",
    ]
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--format",
        choices=("json", "class-ini"),
        default="json",
        help="Output the provenance-rich JSON packet or a CLASS-compatible input fragment.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    manifest = build_manifest()
    if args.format == "class-ini":
        print(render_class_ini(manifest), end="")
    else:
        print(json.dumps(manifest, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
