#!/usr/bin/env python3
"""Execute the source-bounded DAO paper-table reconstruction on six DESI DR2 keys.

Requires the pinned DRMD-CLASS/classy implementation to be installed separately.
The emitted vector is a DASHI reconstruction receipt, not a claim to reproduce the
authors' original MCMC chain state.
"""

import json

from classy import Class
from reconstruct_dark_dimension_dao_paper_table_manifest import build_manifest

DRMD_CLASS_REVISION = "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9"

DESI_KEYS = {
    "lrg1": 0.510,
    "lrg2": 0.706,
    "lrg3_elg1": 0.934,
    "elg2": 1.321,
    "qso": 1.484,
    "lya": 2.330,
}


def classy_parameters(manifest: dict) -> dict:
    p = manifest["parameters"]
    return {
        "omega_b": p["omega_b"],
        "omega_cdm": p["omega_cdm"],
        "H0": p["H0"],
        "A_s": p["A_s"],
        "n_s": p["n_s"],
        "tau_reio": p["tau_reio"],
        "delta_Neff_drmd": p["delta_Neff_drmd"],
        "f_idm_drmd": p["f_idm_drmd"],
        "z_stop": p["z_stop_reconstructed_eq13"],
        "G_over_aH_drmd_ini": p["G_over_aH_drmd_ini"],
        "N_ur": p["N_ur"],
        "N_ncdm": p["N_ncdm"],
        "m_ncdm": p["m_ncdm"],
        "T_ncdm": p["T_ncdm"],
        "YHe": p["YHe"],
        "alpha_s": p["alpha_s"],
        "beta_s": p["beta_s"],
    }


def run_reconstruction() -> dict:
    manifest = build_manifest()
    cosmo = Class()
    computed = False
    try:
        cosmo.set(classy_parameters(manifest))
        cosmo.compute(["thermodynamics"])
        computed = True

        rd = float(cosmo.rs_drag)
        rd_dao = float(cosmo.rs_d_drmd)
        h = float(cosmo.h)
        if not rd > 0.0:
            raise RuntimeError(f"non-positive rs_drag: {rd}")
        if not rd_dao > 0.0:
            raise RuntimeError(f"non-positive rs_d_drmd: {rd_dao}")

        published_rd_bao_mpc_over_h = 100.0
        published_rd_dao_mpc_over_h = 58.6
        reconstructed_rd_bao_mpc_over_h = h * rd
        reconstructed_rd_dao_mpc_over_h = h * rd_dao

        vector = []
        for label, z in DESI_KEYS.items():
            angular_distance = float(cosmo.angular_distance(z))
            hubble_inverse_mpc = float(cosmo.Hubble(z))
            if not hubble_inverse_mpc > 0.0:
                raise RuntimeError(f"non-positive Hubble(z) for {label}: {hubble_inverse_mpc}")

            dm = (1.0 + z) * angular_distance
            dh = 1.0 / hubble_inverse_mpc
            vector.append(
                {
                    "key": label,
                    "z": z,
                    "DM_over_rd": dm / rd,
                    "DH_over_rd": dh / rd,
                }
            )

        return {
            "manifest_kind": "paper-table-reconstruction",
            "upstream_repository": "NEDE-Cosmo/DRMD-CLASS",
            "upstream_revision": DRMD_CLASS_REVISION,
            "original_paper_manifest_claimed": False,
            "equation13_approximation_used": True,
            "published_horizon_cross_check": {
                "published_rd_BAO_Mpc_over_h": 100.0,
                "published_rd_DAO_Mpc_over_h": 58.6,
                "reconstructed_rd_BAO_Mpc_over_h": reconstructed_rd_bao_mpc_over_h,
                "reconstructed_rd_DAO_Mpc_over_h": reconstructed_rd_dao_mpc_over_h,
                "rd_BAO_residual_Mpc_over_h": reconstructed_rd_bao_mpc_over_h
                - published_rd_bao_mpc_over_h,
                "rd_DAO_residual_Mpc_over_h": reconstructed_rd_dao_mpc_over_h
                - published_rd_dao_mpc_over_h,
            },
            "rs_drag_Mpc": rd,
            "rs_d_drmd_Mpc": rd_dao,
            "same_key_vector": vector,
        }
    finally:
        if computed:
            cosmo.struct_cleanup()
        cosmo.empty()


def main() -> None:
    print(json.dumps(run_reconstruction(), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
