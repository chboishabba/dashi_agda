#!/usr/bin/env python3
"""Numerical CKM-from-Yd†Yd diagnostic for the current carrier assumptions.

This mirrors ``YukawaMatrixFullReceipt`` rather than the older diagonal-only
readback: diagonal Heegner self-couplings, nonzero p2-p3 and p3-p5 entries, and
the p2-p5 entry fixed to zero as a diagnostic convention because it remains
open in the receipt.
"""

from __future__ import annotations

import json
import numpy as np


def phase_fix_columns(matrix: np.ndarray) -> np.ndarray:
    fixed = matrix.astype(complex).copy()
    for col in range(fixed.shape[1]):
        pivot = int(np.argmax(np.abs(fixed[:, col])))
        phase = np.angle(fixed[pivot, col])
        fixed[:, col] *= np.exp(-1j * phase)
    return fixed


def main() -> None:
    alpha1 = 0.041240
    y11 = alpha1 * 2 * np.pi
    y22 = alpha1**2 * (4 * np.pi / 3)
    y33 = alpha1**3 * (8 * np.pi / 3)
    y12 = alpha1 * np.pi * np.sqrt(3)
    y23 = alpha1**2 * (14 / np.sqrt(24)) * (8 * np.pi / 3)
    y13 = 0.0  # open p2-p5 entry, set to zero only for this diagnostic.

    yd = np.array(
        [
            [y11, y12, y13],
            [0.0, y22, y23],
            [0.0, 0.0, y33],
        ],
        dtype=float,
    )
    yd_dagger_yd = yd.T @ yd

    eigenvalues, ud = np.linalg.eigh(yd_dagger_yd)
    ud = phase_fix_columns(ud)
    uu = np.eye(3, dtype=complex)
    ckm = uu.conj().T @ ud
    abs_ckm = np.abs(ckm)

    diagnostics = {
        "assumption": "YukawaMatrixFullReceipt with y13=0 diagnostic convention",
        "open_boundary": "p2-p5 y13 remains open; physical CKM promotion is false",
        "alpha1": alpha1,
        "yd": yd.tolist(),
        "yd_dagger_yd": yd_dagger_yd.tolist(),
        "eigenvalues": eigenvalues.tolist(),
        "abs_ckm": abs_ckm.tolist(),
        "comparison_only": {
            "Vus": {"diagnostic": float(abs_ckm[0, 1]), "pdg_sized_target": 0.2245},
            "Vcb": {"diagnostic": float(abs_ckm[1, 2]), "pdg_sized_target": 0.0410},
            "Vub": {"diagnostic": float(abs_ckm[0, 2]), "pdg_sized_target": 0.0037},
            "Vtd": {"diagnostic": float(abs_ckm[2, 0]), "pdg_sized_target": 0.0088},
        },
        "flags": {
            "ckmNumericalDiagonalisationRecorded": True,
            "cabibboAngleDerived": False,
            "physicalCKMPromoted": False,
        },
    }
    print(json.dumps(diagnostics, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
