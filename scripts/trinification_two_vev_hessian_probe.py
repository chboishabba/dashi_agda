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


def selected_vacuum():
    x = np.zeros(36, dtype=float)
    x[2 * 3 + 1] = 1.0          # Phi = E_32
    x[18 + 2 * 3 + 2] = 1.0     # Chi = E_33
    return x


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


def verify():
    x0 = selected_vacuum()
    assert abs(potential_from_real(x0)) < 1e-12
    H = finite_difference_hessian(x0)
    eig = np.linalg.eigvalsh(H)
    rounded = [int(round(float(v))) for v in eig]
    multiplicities = {v: rounded.count(v) for v in sorted(set(rounded))}
    assert multiplicities == {0: 12, 4: 6, 6: 8, 8: 10}
    zero_modes = sum(abs(float(v)) < 1e-5 for v in eig)
    positive_modes = sum(float(v) > 1e-5 for v in eig)
    assert zero_modes == 12 and positive_modes == 24
    return {
        "real_field_dimension": 36,
        "broken_gauge_orbit_dimension": 12,
        "hessian_zero_mode_count": zero_modes,
        "hessian_positive_mode_count": positive_modes,
        "hessian_eigenvalue_multiplicities": multiplicities,
        "accidental_local_flat_directions": False,
        "normalization": "unit coefficients; Phi=E32, Chi=E33",
        "physical_higgs_masses_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
