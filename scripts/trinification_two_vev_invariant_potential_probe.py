#!/usr/bin/env python3
from __future__ import annotations

import numpy as np


def potential_terms(phi, chi):
    a = phi.conj().T @ phi
    b = chi.conj().T @ chi
    al = phi @ phi.conj().T
    bl = chi @ chi.conj().T
    n_phi = float(np.real(np.trace(a)))
    n_chi = float(np.real(np.trace(b)))
    rank_phi = n_phi * n_phi - float(np.real(np.trace(a @ a)))
    rank_chi = n_chi * n_chi - float(np.real(np.trace(b @ b)))
    right_overlap = float(np.real(np.trace(a @ b)))
    left_misalignment = n_phi * n_chi - float(np.real(np.trace(al @ bl)))
    norm_phi = (n_phi - 1.0) ** 2
    norm_chi = (n_chi - 1.0) ** 2
    return {
        "norm_phi": norm_phi,
        "norm_chi": norm_chi,
        "rank_phi": rank_phi,
        "rank_chi": rank_chi,
        "right_overlap": right_overlap,
        "left_misalignment": left_misalignment,
    }


def potential(phi, chi):
    return sum(potential_terms(phi, chi).values())


def random_su3(rng):
    z = rng.normal(size=(3,3)) + 1j * rng.normal(size=(3,3))
    q, r = np.linalg.qr(z)
    phases = np.diag(r)
    phases = phases / np.abs(phases)
    q = q @ np.diag(np.conj(phases))
    det = np.linalg.det(q)
    q = q / np.exp(np.log(det) / 3.0)
    return q


def verify(seed=1729):
    rng = np.random.default_rng(seed)
    e32 = np.zeros((3,3), complex); e32[2,1] = 1
    e33 = np.zeros((3,3), complex); e33[2,2] = 1
    selected = potential(e32, e33)
    assert abs(selected) < 1e-12

    all_nonnegative = True
    all_invariant = True
    all_orbit_zero = True
    for _ in range(256):
        phi = rng.normal(size=(3,3)) + 1j * rng.normal(size=(3,3))
        chi = rng.normal(size=(3,3)) + 1j * rng.normal(size=(3,3))
        terms = potential_terms(phi, chi)
        all_nonnegative &= all(x >= -1e-9 for x in terms.values())

        ul = random_su3(rng)
        ur = random_su3(rng)
        before = potential(phi, chi)
        after = potential(ul @ phi @ ur.conj().T, ul @ chi @ ur.conj().T)
        all_invariant &= abs(before - after) < 1e-8

        orbit_phi = ul @ e32 @ ur.conj().T
        orbit_chi = ul @ e33 @ ur.conj().T
        all_orbit_zero &= abs(potential(orbit_phi, orbit_chi)) < 1e-10

    assert all_nonnegative
    assert all_invariant
    assert all_orbit_zero

    return {
        "selected_pair_potential": 0.0,
        "all_sampled_terms_nonnegative": all_nonnegative,
        "all_sampled_gauge_transforms_preserve_potential": all_invariant,
        "all_sampled_selected_orbit_points_zero": all_orbit_zero,
        "zero_conditions": ["unit_norms", "rank_one", "right_orthogonal", "left_aligned"],
        "trinification_su3l_su3r_invariance_claimed": True,
        "full_e6_invariance_claimed": False,
        "physical_potential_derivation_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
