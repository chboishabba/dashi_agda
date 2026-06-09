#!/usr/bin/env python3
"""Numerical diagnostic for the full Heegner-lane down-type Yukawa matrix.

This script mirrors the constants recorded in
DASHI.Physics.Closure.FullYukawaEigenbasisReceipt.  It is intentionally a
diagnostic helper, not a proof authority.
"""

from __future__ import annotations

import cmath
import json
import math

import numpy as np


ALPHA1 = 0.041240


def main() -> None:
    delta_29 = cmath.phase((1 + 2j * math.sqrt(7)) / (5 + 2j))
    y13_base = 24 * math.pi / math.sqrt(6)

    yd = np.array(
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

    h = yd.conj().T @ yd
    eigenvalues, eigenvectors = np.linalg.eigh(h)
    order = np.argsort(eigenvalues)
    eigenvalues = eigenvalues[order]
    eigenvectors = eigenvectors[:, order]
    abs_ckm = np.abs(eigenvectors)
    jarlskog = np.imag(
        eigenvectors[0, 1]
        * eigenvectors[1, 2]
        * np.conj(eigenvectors[0, 2])
        * np.conj(eigenvectors[1, 1])
    )

    payload = {
        "alpha1": ALPHA1,
        "delta_29_radians": delta_29,
        "y13_base_magnitude": y13_base,
        "yd": [[complex(z).real, complex(z).imag] for row in yd for z in row],
        "yd_dagger_yd": [[complex(z).real, complex(z).imag] for row in h for z in row],
        "eigenvalues": eigenvalues.tolist(),
        "singular_values": [math.sqrt(max(float(v), 0.0)) for v in eigenvalues],
        "abs_ckm_diagnostic": abs_ckm.tolist(),
        "vub_diagnostic": float(abs_ckm[0, 2]),
        "vtd_diagnostic": float(abs_ckm[2, 0]),
        "jarlskog_diagnostic": float(jarlskog),
        "jarlskog_abs_diagnostic": float(abs(jarlskog)),
        "jarlskog_pdg_sized_target": 3.08e-5,
        "jarlskog_pdg_ratio": float(jarlskog / 3.08e-5),
        "flags": {
            "diagnostic_only": True,
            "certified_diagonalisation_constructed": False,
            "jarlskog_invariant_computed": True,
            "cp_violation_diagnostic_recorded": True,
            "physical_ckm_promoted": False,
            "physical_cp_promoted": False,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
