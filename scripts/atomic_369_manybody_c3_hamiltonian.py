#!/usr/bin/env python3
"""Atomic 369 p-shell C3 many-body execution receipt.

This script is a numerical/executable companion to the Agda owners on the
stacked atomic branch.  It checks:

1. cyclic charge transport K has order 3;
2. spatial 120-degree rotation Rz is a different matrix in the magnetic basis;
3. the discrete Fourier basis diagonalizes K to the same C3 character phases;
4. the induced exterior powers wedge^2 K and wedge^3 K have order 3;
5. the hydrogenic n=2,l=1 restricted Hamiltonian H = E_2 I commutes with K
   and its exterior powers;
6. a generic nondegenerate diagonal Hamiltonian does NOT commute with K,
   showing that same-carrier Hamiltonian invariance is a real condition rather
   than a consequence of having three states.

Attribution boundary:
- hydrogenic degeneracy for fixed n,l is conventional central-Coulomb physics
  already sourced on the parent branch to NIST DLMF;
- DASHI owns this matrix reconstruction/execution;
- no Li/Be, NH3, CoTa4Se8, Monster, or full-atom Hamiltonian is identified with
  this selected p-shell carrier by this script.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np


OUT = Path("generated/atomic_369_manybody_c3_receipt.json")


def compound_matrix_2(a: np.ndarray) -> np.ndarray:
    """Second exterior power in basis (01, 02, 12)."""
    pairs = [(0, 1), (0, 2), (1, 2)]
    out = np.empty((3, 3), dtype=complex)
    for r, (i, j) in enumerate(pairs):
        for c, (k, l) in enumerate(pairs):
            out[r, c] = np.linalg.det(a[np.ix_([i, j], [k, l])])
    return out


def main() -> None:
    omega = np.exp(2j * np.pi / 3)

    # Ordered magnetic/residue basis (-1, 0, +1).
    K = np.array(
        [
            [0, 0, 1],
            [1, 0, 0],
            [0, 1, 0],
        ],
        dtype=complex,
    )

    # Spatial z rotation in the complex magnetic basis.
    Rz = np.diag([omega**-1, 1.0, omega])

    # Standard DFT columns have eigenvalues (1, omega^-1, omega).  Reorder to
    # magnetic frequency order (-1, 0, +1).
    F0 = np.array(
        [
            [1, 1, 1],
            [1, omega, omega**2],
            [1, omega**2, omega],
        ],
        dtype=complex,
    ) / np.sqrt(3)
    Fmag = F0[:, [1, 0, 2]]

    diagonalized = Fmag.conj().T @ K @ Fmag

    W2 = compound_matrix_2(K)
    W3 = np.array([[np.linalg.det(K)]], dtype=complex)

    # Hydrogenic E_2 = -1/(2 n^2) Hartree at n=2, used only as a scalar label.
    E2 = -1.0 / 8.0
    H1 = E2 * np.eye(3, dtype=complex)
    H2 = 2 * E2 * np.eye(3, dtype=complex)
    H3 = 3 * E2 * np.eye(1, dtype=complex)

    # Deliberate control: three unequal energies on the same carrier.
    H_bad = np.diag([-0.20, -0.125, -0.08]).astype(complex)

    receipt = {
        "basis_order": ["m=-1", "m=0", "m=+1"],
        "charge_K_order3_residual": float(np.linalg.norm(np.linalg.matrix_power(K, 3) - np.eye(3))),
        "spatial_Rz_order3_residual": float(np.linalg.norm(np.linalg.matrix_power(Rz, 3) - np.eye(3))),
        "same_basis_K_minus_Rz_norm": float(np.linalg.norm(K - Rz)),
        "same_basis_commutator_norm": float(np.linalg.norm(K @ Rz - Rz @ K)),
        "fourier_unitarity_residual": float(np.linalg.norm(Fmag.conj().T @ Fmag - np.eye(3))),
        "fourier_diagonalization_residual": float(np.linalg.norm(diagonalized - Rz)),
        "wedge2_order3_residual": float(np.linalg.norm(np.linalg.matrix_power(W2, 3) - np.eye(3))),
        "wedge3_value": [float(W3[0, 0].real), float(W3[0, 0].imag)],
        "wedge3_order3_residual": float(np.linalg.norm(np.linalg.matrix_power(W3, 3) - np.eye(1))),
        "hydrogenic_p_triplet_commutator_norm": float(np.linalg.norm(H1 @ K - K @ H1)),
        "hydrogenic_wedge2_commutator_norm": float(np.linalg.norm(H2 @ W2 - W2 @ H2)),
        "hydrogenic_wedge3_commutator_norm": float(np.linalg.norm(H3 @ W3 - W3 @ H3)),
        "nondegenerate_control_commutator_norm": float(np.linalg.norm(H_bad @ K - K @ H_bad)),
        "boundaries": {
            "fourier_equivalent_not_same_matrix": True,
            "exterior_basis_action_paid": True,
            "hydrogenic_restricted_shell_commutation_paid": True,
            "electron_electron_interacting_p_shell_hamiltonian_paid": False,
            "li_be_scf_same_carrier_as_p_triplet": False,
            "ammonia_hamiltonian_same_carrier_as_atomic_p_triplet": False,
            "material_hamiltonian_same_carrier_as_atomic_p_triplet": False,
            "full_atom_369_identity_paid": False,
        },
    }

    if receipt["fourier_diagonalization_residual"] > 1e-12:
        raise RuntimeError("Fourier diagonalization failed")
    if receipt["wedge2_order3_residual"] > 1e-12:
        raise RuntimeError("wedge^2 action is not order three")
    if receipt["hydrogenic_p_triplet_commutator_norm"] > 1e-12:
        raise RuntimeError("restricted p-shell Hamiltonian failed C3 commutation")
    if receipt["nondegenerate_control_commutator_norm"] <= 1e-6:
        raise RuntimeError("negative-control Hamiltonian unexpectedly commutes")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
