#!/usr/bin/env python3
"""Physical mass-matrix diagnostic from the current carrier Yukawa surface.

This is a numerical diagnostic only.  It applies the PDG electroweak VEV as an
external calibration, then reports singular values of M_d = Y_d v/sqrt(2).
"""

from __future__ import annotations

import json
import math

import numpy as np


ALPHA1 = 0.041240
VEV_GEV = 246.22
DELTA_29 = 1.003510488600938


def carrier_yukawa() -> np.ndarray:
    y13 = (ALPHA1**3) * (24 * math.pi / math.sqrt(6)) * complex(
        math.cos(DELTA_29), math.sin(DELTA_29)
    )
    return np.array(
        [
            [ALPHA1 * (2 * math.pi), ALPHA1 * math.pi * math.sqrt(3), y13],
            [
                0.0,
                (ALPHA1**2) * (4 * math.pi / 3),
                (ALPHA1**2) * (14 / math.sqrt(24)) * (8 * math.pi / 3),
            ],
            [0.0, 0.0, (ALPHA1**3) * (8 * math.pi / 3)],
        ],
        dtype=complex,
    )


def main() -> None:
    scale = VEV_GEV / math.sqrt(2)
    yd = carrier_yukawa()
    md = yd * scale
    mass_squared, ud = np.linalg.eigh(md.conj().T @ md)
    order = np.argsort(mass_squared)
    mass_squared = mass_squared[order]
    masses = np.sqrt(np.maximum(mass_squared, 0.0))
    pdg = np.array([0.00467, 0.0934, 4.18])

    diagnostics = {
        "alpha1": ALPHA1,
        "vev_gev_pdg_input": VEV_GEV,
        "scale_v_over_sqrt2_gev": scale,
        "mass_eigenvalues_gev": masses.tolist(),
        "mass_squared_eigenvalues_gev2": mass_squared.tolist(),
        "pdg_comparison_gev": {
            "md": 0.00467,
            "ms": 0.0934,
            "mb": 4.18,
        },
        "mass_over_pdg": (masses / pdg).tolist(),
        "flags": {
            "physicalMassEigenvaluesComputed": True,
            "physicalMassMatchesPDG": False,
            "physicalCKMPromoted": False,
        },
    }
    print(json.dumps(diagnostics, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
