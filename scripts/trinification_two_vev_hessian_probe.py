#!/usr/bin/env python3
from __future__ import annotations

import math
import numpy as np


def potential_terms(phi, chi):
    a = phi.conj().T @ phi
    b = chi.conj().T @ chi
    al = phi @ phi.conj().T
    bl = chi @ chi.conj().T
    n_phi = float(np.real(np.trace(a)))
    n_chi = float(np.real(np.trace(b)))
    return [
        (n_phi - 1.0) ** 2,
        (n_chi - 1.0) ** 2,
        n_phi * n_phi - float(np.real(np.trace(a @ a))),
        n_chi * n_chi - float(np.real(np.trace(b @ b))),
        float(np.real(np.trace(a @ b))),
        n_phi * n_chi - float(np.real(np.trace(al @ bl))),
    ]


def potential_from_real(x):
    pr = x[0:9].reshape(3, 3)
    pi = x[9:18].reshape(3, 3)
    cr = x[18:27].reshape(3, 3)
    ci = x[27:36].reshape(3, 3)
    return float(sum(potential_terms(pr + 1j * pi, cr + 1j * ci)))


def selected_matrices():
    phi = np.zeros((3, 3), complex); phi[2, 1] = 1
    chi = np.zeros((3, 3), complex); chi[2, 2] = 1
    return phi, chi


def selected_vacuum():
    phi, chi = selected_matrices()
    return pair_to_real(phi, chi)


def pair_to_real(phi, chi):
    return np.concatenate([
        phi.real.reshape(-1), phi.imag.reshape(-1),
        chi.real.reshape(-1), chi.imag.reshape(-1),
    ])


def finite_difference_hessian(x, h=1e-4):
    n = len(x)
    H = np.zeros((n, n), dtype=float)
    f0 = potential_from_real(x)
    for i in range(n):
        ei = np.zeros(n); ei[i] = h
        H[i, i] = (potential_from_real(x + ei) - 2 * f0 + potential_from_real(x - ei)) / h**2
    for i in range(n):
        for j in range(i + 1, n):
            ei = np.zeros(n); ej = np.zeros(n)
            ei[i] = h; ej[j] = h
            H[i, j] = H[j, i] = (
                potential_from_real(x + ei + ej)
                - potential_from_real(x + ei - ej)
                - potential_from_real(x - ei + ej)
                + potential_from_real(x - ei - ej)
            ) / (4 * h**2)
    return H


def su3_generators():
    lam = [
        np.array([[0,1,0],[1,0,0],[0,0,0]], complex),
        np.array([[0,-1j,0],[1j,0,0],[0,0,0]], complex),
        np.array([[1,0,0],[0,-1,0],[0,0,0]], complex),
        np.array([[0,0,1],[0,0,0],[1,0,0]], complex),
        np.array([[0,0,-1j],[0,0,0],[1j,0,0]], complex),
        np.array([[0,0,0],[0,0,1],[0,1,0]], complex),
        np.array([[0,0,0],[0,0,-1j],[0,1j,0]], complex),
        np.array([[1,0,0],[0,1,0],[0,0,-2]], complex) / math.sqrt(3),
    ]
    return [x / 2 for x in lam]


def gauge_orbit_tangent_matrix():
    phi, chi = selected_matrices()
    cols = []
    for t in su3_generators():
        cols.append(pair_to_real(1j * t @ phi, 1j * t @ chi))
    for t in su3_generators():
        cols.append(pair_to_real(-1j * phi @ t, -1j * chi @ t))
    return np.stack(cols, axis=1)


def verify():
    x0 = selected_vacuum()
    assert abs(potential_from_real(x0)) < 1e-12
    H = finite_difference_hessian(x0)
    eig, eigvec = np.linalg.eigh(H)
    rounded = [int(round(float(v))) for v in eig]
    multiplicities = {v: rounded.count(v) for v in sorted(set(rounded))}
    assert multiplicities == {0: 12, 4: 6, 6: 8, 8: 10}
    zero_modes = sum(abs(float(v)) < 1e-5 for v in eig)
    positive_modes = sum(float(v) > 1e-5 for v in eig)
    assert zero_modes == 12 and positive_modes == 24

    tangent = gauge_orbit_tangent_matrix()
    tangent_rank = int(np.linalg.matrix_rank(tangent, tol=1e-8))
    assert tangent_rank == 12
    annihilation_norm = float(np.linalg.norm(H @ tangent))
    assert annihilation_norm < 1e-5

    # Same-subspace test, not merely equal dimensions: compare orthonormal bases
    # for the gauge-orbit tangent and Hessian nullspace via principal angles.
    u, _, _ = np.linalg.svd(tangent, full_matrices=False)
    q_tangent = u[:, :tangent_rank]
    q_kernel = eigvec[:, np.abs(eig) < 1e-5]
    principal_cosines = np.linalg.svd(q_tangent.T @ q_kernel, compute_uv=False)
    same_subspace = (
        len(principal_cosines) == 12
        and float(np.max(np.abs(principal_cosines - 1.0))) < 1e-8
    )
    assert same_subspace

    return {
        "real_field_dimension": 36,
        "broken_gauge_orbit_dimension": 12,
        "gauge_orbit_tangent_rank": tangent_rank,
        "hessian_zero_mode_count": zero_modes,
        "hessian_positive_mode_count": positive_modes,
        "hessian_eigenvalue_multiplicities": multiplicities,
        "gauge_tangent_annihilated_by_hessian": True,
        "gauge_tangent_hessian_residual_norm": annihilation_norm,
        "hessian_kernel_equals_gauge_orbit_tangent": same_subspace,
        "accidental_local_flat_directions": False,
        "normalization": "unit coefficients; Phi=E32, Chi=E33",
        "physical_higgs_masses_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
