#!/usr/bin/env python3
"""Corrected radial-state identity regression for the DASHI atomic lane.

Purpose:
  Repair the archive defect where solve_orbital(r, Z, l, V_H) discarded n and
  always selected the lowest eigenpair for l.

This producer validates the n-sensitive selector in the analytically controlled
hydrogenic limit V_H = 0. For a bound state (n,l), the radial eigenpair index is
n-l-1. The script solves all required states for each l in one tridiagonal
diagonalization, preserving orthogonality within that l-sector.

This is a numerical regression for radial identity only. It is not an SCF,
Hartree-Fock, correlated-atom, or empirical periodic-table recovery theorem.
"""

import argparse
import hashlib
import json
import platform
from pathlib import Path

import numpy as np
import scipy
from scipy.linalg import eigh_tridiagonal


def radial_grid(rmax: float, npts: int):
    dr = rmax / (npts + 1)
    r = dr * np.arange(1, npts + 1, dtype=float)
    return r, dr


def radial_hamiltonian(r, dr, Z: int, l: int, extra_potential=None):
    if extra_potential is None:
        extra_potential = np.zeros_like(r)
    diag = (
        1.0 / dr**2
        + l * (l + 1) / (2.0 * r**2)
        - Z / r
        + extra_potential
    )
    off = -0.5 / dr**2 * np.ones(len(r) - 1)
    return diag, off


def radial_state_index(n: int, l: int) -> int:
    if n < 1 or l < 0 or l >= n:
        raise ValueError(f"invalid bound-state labels n={n}, l={l}")
    return n - l - 1


def solve_l_sector(r, dr, Z: int, l: int, max_state_index: int):
    diag, off = radial_hamiltonian(r, dr, Z, l)
    vals, vecs = eigh_tridiagonal(
        diag,
        off,
        select="i",
        select_range=(0, max_state_index),
        check_finite=True,
    )
    # Euclidean eigenvectors from eigh_tridiagonal are mutually orthonormal.
    # Scale by sqrt(dr) so discrete radial integration is approximately unity.
    vecs = vecs / np.sqrt(dr)
    return vals, vecs


def count_nodes(u, relative_cutoff=1e-5):
    threshold = relative_cutoff * np.max(np.abs(u))
    v = u[np.abs(u) > threshold]
    if len(v) < 2:
        return 0
    s = np.sign(v)
    return int(np.sum(s[1:] * s[:-1] < 0))


def hydrogenic_energy(Z: int, n: int) -> float:
    return -(Z * Z) / (2.0 * n * n)


def build_receipt(rmax=80.0, npts=4000, energy_tolerance=5e-4):
    r, dr = radial_grid(rmax, npts)
    targets = [(1, 0), (2, 0), (3, 0), (2, 1), (3, 1), (3, 2)]
    by_l = {}
    for n, l in targets:
        by_l.setdefault(l, 0)
        by_l[l] = max(by_l[l], radial_state_index(n, l))

    solved = {}
    sector_vectors = {}
    for l, max_index in by_l.items():
        vals, vecs = solve_l_sector(r, dr, 1, l, max_index)
        sector_vectors[l] = vecs
        for n, ll in targets:
            if ll == l:
                idx = radial_state_index(n, l)
                solved[(n, l)] = (float(vals[idx]), vecs[:, idx])

    states = []
    all_energy_checks = True
    all_node_checks = True
    for n, l in targets:
        energy, u = solved[(n, l)]
        expected = hydrogenic_energy(1, n)
        error = abs(energy - expected)
        nodes = count_nodes(u)
        expected_nodes = radial_state_index(n, l)
        energy_ok = error <= energy_tolerance
        nodes_ok = nodes == expected_nodes
        all_energy_checks &= energy_ok
        all_node_checks &= nodes_ok
        states.append(
            {
                "n": n,
                "l": l,
                "radial_state_index": expected_nodes,
                "energy_hartree": energy,
                "analytic_energy_hartree": expected,
                "absolute_error_hartree": error,
                "observed_nodes": nodes,
                "energy_ok": bool(energy_ok),
                "nodes_ok": bool(nodes_ok),
            }
        )

    orthogonality = {}
    all_orthogonality_checks = True
    for l, vecs in sector_vectors.items():
        gram = dr * (vecs.T @ vecs)
        max_abs_error = float(np.max(np.abs(gram - np.eye(gram.shape[0]))))
        ok = max_abs_error <= 1e-10
        all_orthogonality_checks &= ok
        orthogonality[str(l)] = {
            "state_count": int(gram.shape[0]),
            "max_abs_gram_error": max_abs_error,
            "ok": bool(ok),
        }

    identity_distinct = (
        radial_state_index(1, 0) != radial_state_index(2, 0)
        and radial_state_index(2, 0) != radial_state_index(3, 0)
    )

    return {
        "producer": "scripts/atomic_radial_identity_repair.py",
        "purpose": "n-sensitive radial eigenstate identity regression in the hydrogenic limit",
        "Z": 1,
        "rmax_bohr": rmax,
        "npts": npts,
        "energy_tolerance_hartree": energy_tolerance,
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "scipy_version": scipy.__version__,
        "states": states,
        "orthogonality_by_l": orthogonality,
        "same_l_principal_identity_distinguished": bool(identity_distinct),
        "all_energy_checks": bool(all_energy_checks),
        "all_node_checks": bool(all_node_checks),
        "all_orthogonality_checks": bool(all_orthogonality_checks),
        "passed": bool(
            identity_distinct
            and all_energy_checks
            and all_node_checks
            and all_orthogonality_checks
        ),
        "non_promotion_boundary": (
            "This receipt validates radial-state identity and hydrogenic numerical "
            "regressions only; it does not establish SCF convergence, many-electron "
            "ground states, calibrated ionization energies, nuclear stability, or "
            "empirical periodic-table recovery."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rmax", type=float, default=80.0)
    parser.add_argument("--npts", type=int, default=4000)
    parser.add_argument("--energy-tolerance", type=float, default=5e-4)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    receipt = build_receipt(args.rmax, args.npts, args.energy_tolerance)
    script_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    receipt["producer_sha256"] = script_hash

    text = json.dumps(receipt, indent=2, sort_keys=True)
    print(text)
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text + "\n", encoding="utf-8")
    raise SystemExit(0 if receipt["passed"] else 1)


if __name__ == "__main__":
    main()
