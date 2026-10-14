#!/usr/bin/env python3
from __future__ import annotations

import math
import numpy as np


def generators():
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


def mass_matrix(vevs):
    t = generators()
    columns = []
    for side in ("L", "R"):
        for a in range(8):
            pieces = []
            for z in vevs:
                dz = t[a] @ z if side == "L" else -z @ t[a]
                pieces.append(dz.reshape(-1))
            columns.append(np.concatenate(pieces))
    d = np.asarray(columns).T
    return np.real(d.conj().T @ d)


def multiplicities(values, tol=1e-9):
    targets = [(0.25, "1/4"), (0.5, "1/2"), (5/6, "5/6")]
    return {label: sum(abs(float(x) - target) < tol for x in values) for target, label in targets}


def verify():
    e32 = np.zeros((3,3), complex); e32[2,1] = 1
    e33 = np.zeros((3,3), complex); e33[2,2] = 1

    single = mass_matrix([e33])
    double = mass_matrix([e32, e33])
    single_rank = int(np.linalg.matrix_rank(single, tol=1e-9))
    double_rank = int(np.linalg.matrix_rank(double, tol=1e-9))
    assert single_rank == 9
    assert double_rank == 12

    eig = np.linalg.eigvalsh(double)
    positive = [x for x in eig if x > 1e-9]
    mult = multiplicities(positive)
    assert mult == {"1/4": 4, "1/2": 7, "5/6": 1}

    t = generators()
    # Existing trinification hypercharge direction, up to an overall -1/6:
    # H = X_L + 3 T3_R(full-diagonal convention) + X_R.
    x_l = 2 * math.sqrt(3) * t[7]
    x_r = 2 * math.sqrt(3) * t[7]
    t3r_full = 2 * t[2]
    h_l = x_l
    h_r = x_r + 3 * t3r_full
    hypercharge_survives = all(np.allclose(h_l @ z - z @ h_r, 0, atol=1e-10) for z in (e32, e33))
    assert hypercharge_survives

    # SU(2)_L acts on the first two left rows and leaves row 3 fixed.
    su2l_survives = all(
        np.allclose(t[a] @ z, 0, atol=1e-10)
        for a in (0,1,2)
        for z in (e32, e33)
    )
    assert su2l_survives

    return {
        "single_vev_stabilizer_dimension": 16 - single_rank,
        "two_vev_stabilizer_dimension": 16 - double_rank,
        "two_vev_mass_rank": double_rank,
        "unbroken_generators": ["SU2L_1", "SU2L_2", "SU2L_3", "Y"],
        "hypercharge_generator_survives": hypercharge_survives,
        "positive_mass_eigenvalue_multiplicities": mult,
        "normalization": "T_a=lambda_a/2, g_L=g_R=v_32=v_33=1",
        "color_untouched": True,
        "physical_scale_and_couplings_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
