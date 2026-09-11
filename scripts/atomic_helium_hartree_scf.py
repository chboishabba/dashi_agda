#!/usr/bin/env python3
"""Restricted closed-shell radial Hartree producer for neutral helium.

This is the first many-electron producer after the radial-identity repair.  It
uses one spatial 1s orbital occupied by two opposite-spin electrons.  Each
electron sees the Coulomb field of the other electron, so the Hartree potential
is built from one normalized orbital density rather than the full two-electron
density; this avoids the obvious one-electron self-interaction present in the
archived toy solver.

The producer emits SCF convergence diagnostics, neutral He total energy, He+
energy on the same radial grid, and IE1 = E(He+) - E(He), then compares to NIST
ASD.  It is Hartree-level only: electron correlation, finite nuclear mass,
relativistic/QED effects and higher-order corrections remain unpaid.
"""

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy.linalg import eigh_tridiagonal

HARTREE_EV_2022_CODATA = 27.211386245981
NIST_HEI_IE_EV = 24.587389011
NIST_HEI_IE_UNCERTAINTY_EV = 0.000000025


def radial_grid(rmax: float, npts: int):
    dr = rmax / (npts + 1)
    r = dr * np.arange(1, npts + 1, dtype=float)
    return r, dr


def radial_hamiltonian(r, dr, Z: int, l: int, potential):
    diag = (
        1.0 / dr**2
        + l * (l + 1) / (2.0 * r**2)
        - Z / r
        + potential
    )
    off = -0.5 / dr**2 * np.ones(len(r) - 1)
    return diag, off


def normalize_radial(u, dr):
    return u / np.sqrt(np.sum(u * u) * dr)


def solve_lowest(r, dr, Z: int, l: int, potential):
    diag, off = radial_hamiltonian(r, dr, Z, l, potential)
    vals, vecs = eigh_tridiagonal(
        diag, off, select="i", select_range=(0, 0), check_finite=True
    )
    return float(vals[0]), normalize_radial(vecs[:, 0], dr)


def hartree_potential_one_electron(r, dr, u):
    # For normalized radial u, rho(r)=|u(r)|^2/(4*pi*r^2).  The spherical
    # Coulomb potential is (1/r) int_0^r |u|^2 dr' + int_r^inf |u|^2/r' dr'.
    radial_probability = u * u
    enclosed = np.cumsum(radial_probability) * dr
    outside = np.cumsum((radial_probability / r)[::-1]) * dr
    outside = outside[::-1]
    return enclosed / r + outside


def run_helium_hartree(
    npts: int,
    rmax: float,
    mixing: float,
    tolerance: float,
    max_iterations: int,
):
    r, dr = radial_grid(rmax, npts)
    potential = np.zeros_like(r)
    convergence = []

    for iteration in range(1, max_iterations + 1):
        orbital_energy, u = solve_lowest(r, dr, 2, 0, potential)
        new_potential = hartree_potential_one_electron(r, dr, u)
        max_delta = float(np.max(np.abs(new_potential - potential)))
        convergence.append(max_delta)
        potential = (1.0 - mixing) * potential + mixing * new_potential
        if max_delta < tolerance:
            break
    else:
        raise RuntimeError("helium Hartree SCF did not converge")

    orbital_energy, u = solve_lowest(r, dr, 2, 0, potential)
    physical_hartree = hartree_potential_one_electron(r, dr, u)
    coulomb_J = float(np.sum((u * u) * physical_hartree) * dr)
    total_energy_he = 2.0 * orbital_energy - coulomb_J

    he_plus_energy, _ = solve_lowest(r, dr, 2, 0, np.zeros_like(r))
    ionization_hartree = he_plus_energy - total_energy_he
    ionization_ev = ionization_hartree * HARTREE_EV_2022_CODATA

    return {
        "npts": npts,
        "rmax_bohr": rmax,
        "mixing": mixing,
        "tolerance": tolerance,
        "iterations": iteration,
        "final_max_potential_delta": convergence[-1],
        "helium_1s_orbital_energy_hartree": orbital_energy,
        "helium_coulomb_J_hartree": coulomb_J,
        "helium_total_energy_hartree": total_energy_he,
        "he_plus_total_energy_hartree": he_plus_energy,
        "ionization_energy_hartree": ionization_hartree,
        "ionization_energy_ev": ionization_ev,
        "nist_helium_ionization_energy_ev": NIST_HEI_IE_EV,
        "minus_nist_ev": ionization_ev - NIST_HEI_IE_EV,
        "relative_residual": (ionization_ev - NIST_HEI_IE_EV) / NIST_HEI_IE_EV,
        "converged": True,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--npts", type=int, default=32000)
    parser.add_argument("--rmax", type=float, default=40.0)
    parser.add_argument("--mixing", type=float, default=0.3)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    parser.add_argument("--max-iterations", type=int, default=300)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    result = run_helium_hartree(
        args.npts, args.rmax, args.mixing, args.tolerance, args.max_iterations
    )
    receipt = {
        "producer": "scripts/atomic_helium_hartree_scf.py",
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "model": "restricted closed-shell spherical Hartree for He 1s^2",
        "python_version": __import__("platform").python_version(),
        "numpy_version": np.__version__,
        "scipy_version": scipy.__version__,
        "nist_asd_doi": "10.18434/T4W30F",
        "nist_ground_shell": "1s2",
        "nist_ionization_energy_ev": NIST_HEI_IE_EV,
        "nist_uncertainty_ev": NIST_HEI_IE_UNCERTAINTY_EV,
        "self_interaction_policy": (
            "each electron sees the spherical Coulomb field of one other electron; "
            "total energy E=2*epsilon-J"
        ),
        "result": result,
        "passed": bool(result["converged"]),
        "unpaid_physics": [
            "electron correlation beyond a single Hartree product",
            "finite helium nuclear mass",
            "relativistic and radiative/QED corrections",
            "exchange/correlation treatment for non-opposite-spin or multi-orbital atoms",
            "generic state tracking across multiple occupied subshells",
        ],
        "non_promotion_boundary": (
            "This is a same-object closed-shell helium Hartree execution and NIST "
            "diagnostic. Its residual is expected to remain large because correlation "
            "and other corrections are unpaid; it is not full periodic-table recovery."
        ),
    }

    text = json.dumps(receipt, indent=2, sort_keys=True)
    print(text)
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text + "\n", encoding="utf-8")
    raise SystemExit(0 if receipt["passed"] else 1)


if __name__ == "__main__":
    main()
