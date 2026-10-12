"""Executable Sah et al. four-site Y-sublattice tight-binding donor.

Primary source:
  Avinash Sah et al., npj Quantum Materials 11, 63 (2026)
  DOI 10.1038/s41535-026-00885-5, Eq. (1), Fig. 5.

This is the paper's qualitative hexagonal -> kagome-like -> ideal-kagome
Hamiltonian.  It is NOT the material-specific CoTa4Se8 ab-initio/Wannier
Hamiltonian and therefore cannot close the material-H leaf by itself.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np


def sublattice_vectors(a: float = 1.0):
    return (
        np.array([a, 0.0]),
        np.array([0.5 * a, math.sqrt(3.0) * 0.5 * a]),
        np.array([-0.5 * a, math.sqrt(3.0) * 0.5 * a]),
    )


def hamiltonian(kx: float, ky: float, *, t: float = 1.0,
                tprime: float = -0.4, eps1: float = -2.2,
                eps2: float = 0.0, eps3: float = 0.0,
                eps4: float = 0.0, a: float = 1.0) -> np.ndarray:
    """Eq. (1) of Sah et al., in the ordered basis Y1,Y2,Y3,Y4."""
    k = np.array([kx, ky], dtype=float)
    a1, a2, a3 = sublattice_vectors(a)
    c1, c2, c3 = (math.cos(float(k @ v)) for v in (a1, a2, a3))
    h = np.array([
        [eps1,          -2*tprime*c1, -2*tprime*c2, -2*tprime*c3],
        [-2*tprime*c1,  eps2,         -2*t*c3,      -2*t*c2],
        [-2*tprime*c2, -2*t*c3,       eps3,         -2*t*c1],
        [-2*tprime*c3, -2*t*c2,      -2*t*c1,       eps4],
    ], dtype=float)
    return h


def eigenvalues(kx: float, ky: float, **params):
    return np.linalg.eigvalsh(hamiltonian(kx, ky, **params))


def audit(grid_n: int = 41):
    grid = np.linspace(-math.pi, math.pi, grid_n)
    fixtures = {
        "hexagonal": dict(t=1.0, tprime=1.0, eps1=0.0),
        "kagome_like": dict(t=1.0, tprime=-0.4, eps1=-2.2),
        "ideal_kagome": dict(t=1.0, tprime=0.0, eps1=-100.0),
    }
    out = {}
    for name, params in fixtures.items():
        bands = []
        max_hermiticity_defect = 0.0
        for kx in grid:
            for ky in grid:
                h = hamiltonian(kx, ky, **params)
                max_hermiticity_defect = max(
                    max_hermiticity_defect,
                    float(np.max(np.abs(h - h.T.conj()))),
                )
                bands.append(np.linalg.eigvalsh(h))
        bands = np.asarray(bands)
        out[name] = {
            "parameters": params,
            "band_min_over_grid": bands.min(axis=0).tolist(),
            "band_max_over_grid": bands.max(axis=0).tolist(),
            "bandwidth_over_grid": np.ptp(bands, axis=0).tolist(),
            "max_hermiticity_defect": max_hermiticity_defect,
        }

    # In the exact t'=0 limit, Y1 is decoupled and the remaining kagome block
    # has a momentum-independent eigenvalue +2t.  Check the numerical fixture
    # over the full grid rather than relying on one high-symmetry path.
    ideal = out["ideal_kagome"]
    assert ideal["max_hermiticity_defect"] == 0.0
    assert abs(ideal["bandwidth_over_grid"][0]) < 1e-12  # decoupled eps1
    assert abs(ideal["bandwidth_over_grid"][3]) < 1e-12  # kagome flat band
    assert abs(ideal["band_min_over_grid"][3] - 2.0) < 1e-12
    assert abs(ideal["band_max_over_grid"][3] - 2.0) < 1e-12

    # The source's kagome-like parameter choice strongly flattens the upper
    # band relative to the fully connected hexagonal fixture on this grid.
    assert out["kagome_like"]["bandwidth_over_grid"][3] < out["hexagonal"]["bandwidth_over_grid"][3]

    return {
        "source_doi": "10.1038/s41535-026-00885-5",
        "equation": 1,
        "grid_n": grid_n,
        "fixtures": out,
        "ideal_kagome_flat_band_eigenvalue_over_t": 2.0,
        "epistemic_boundary": (
            "exact execution of the published qualitative four-site TB donor; "
            "not the CoTa4Se8 ab-initio/Wannier Hamiltonian, not an ARPES fit"
        ),
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--grid-n", type=int, default=41)
    p.add_argument("--receipt")
    args = p.parse_args()
    result = audit(args.grid_n)
    if args.receipt:
        Path(args.receipt).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
