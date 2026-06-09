#!/usr/bin/env python3
"""CKM diagnostic from the physical down-type mass matrix.

The physical down-type mass matrix is M_d = Y_d * v / sqrt(2).  Since this is
a global positive scaling of Y_d, the eigenvectors of M_d^dagger M_d are the
same as the eigenvectors of Y_d^dagger Y_d.  This script verifies that the
diagnostic CKM absolute values match the FullYukawaEigenbasis diagnostic.
"""

from __future__ import annotations

import cmath
import json
import math

import numpy as np


ALPHA1 = 0.041240
VEV_GEV = 246.22

EXPECTED_ABS_CKM = np.array(
    [
        [0.6486646808181262, 0.08976502640935104, 0.7557621132954778],
        [0.7496905973872523, 0.09589115634857709, 0.6548044702987887],
        [0.13114167929481035, 0.9913360309036799, 0.00739822842820142],
    ]
)


def full_yukawa_matrix() -> np.ndarray:
    delta_29 = cmath.phase((1 + 2j * math.sqrt(7)) / (5 + 2j))
    y13_base = 24 * math.pi / math.sqrt(6)
    return np.array(
        [
            [
                ALPHA1 * 2 * math.pi,
                ALPHA1 * math.pi * math.sqrt(3),
                (ALPHA1**3) * y13_base * cmath.exp(1j * delta_29),
            ],
            [
                0,
                (ALPHA1**2) * 4 * math.pi / 3,
                (ALPHA1**2) * (14 / math.sqrt(24)) * (8 * math.pi / 3),
            ],
            [0, 0, (ALPHA1**3) * 8 * math.pi / 3],
        ],
        dtype=complex,
    )


def sorted_abs_eigenvectors(hermitian: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(hermitian)
    order = np.argsort(eigenvalues)
    return np.abs(eigenvectors[:, order])


def main() -> None:
    yd = full_yukawa_matrix()
    md = yd * (VEV_GEV / math.sqrt(2))

    abs_ckm_from_yukawa = sorted_abs_eigenvectors(yd.conj().T @ yd)
    abs_ckm_from_mass = sorted_abs_eigenvectors(md.conj().T @ md)

    max_scaling_difference = float(
        np.max(np.abs(abs_ckm_from_mass - abs_ckm_from_yukawa))
    )
    max_full_receipt_difference = float(
        np.max(np.abs(abs_ckm_from_mass - EXPECTED_ABS_CKM))
    )

    if max_scaling_difference > 1e-12:
        raise SystemExit(
            f"global mass scaling changed eigenvectors: {max_scaling_difference}"
        )
    if max_full_receipt_difference > 1e-12:
        raise SystemExit(
            "mass-matrix CKM values diverge from FullYukawaEigenbasis "
            f"diagnostic: {max_full_receipt_difference}"
        )

    payload = {
        "mass_matrix_formula": "M_d = Y_d * v / sqrt(2)",
        "vev_GeV": VEV_GEV,
        "global_scaling_changes_ckm_eigenvectors": False,
        "max_scaling_difference": max_scaling_difference,
        "max_full_yukawa_eigenbasis_difference": max_full_receipt_difference,
        "abs_ckm": abs_ckm_from_mass.tolist(),
        "abs_ckm_ppm_rounded": np.rint(abs_ckm_from_mass * 1_000_000)
        .astype(int)
        .tolist(),
        "pdg_comparison_only": {
            "Vus": {"diagnostic": float(abs_ckm_from_mass[0, 1]), "pdg": 0.2245},
            "Vcb": {"diagnostic": float(abs_ckm_from_mass[1, 2]), "pdg": 0.0410},
            "Vub": {"diagnostic": float(abs_ckm_from_mass[0, 2]), "pdg": 0.0037},
            "Vtd": {"diagnostic": float(abs_ckm_from_mass[2, 0]), "pdg": 0.0088},
            "Vts": {"diagnostic": float(abs_ckm_from_mass[2, 1]), "pdg": 0.0405},
            "Vtb": {"diagnostic": float(abs_ckm_from_mass[2, 2]), "pdg": 0.9991},
        },
        "flags": {
            "diagnostic_only": True,
            "aligned_with_full_yukawa_eigenbasis": True,
            "physicalCKMPromoted": False,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
