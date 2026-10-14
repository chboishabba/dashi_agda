#!/usr/bin/env python3
from __future__ import annotations

import itertools
import numpy as np

P = 3
POINTS = tuple(itertools.product(range(P), repeat=2))
INDEX = {p: i for i, p in enumerate(POINTS)}
NORM_ONE = ((1, 0), (2, 0), (0, 1), (0, 2))


def matmul_mod3(a, b):
    return np.asarray(a, dtype=int) @ np.asarray(b, dtype=int) % P


def orthogonal_linear_parts():
    out = []
    eye = np.eye(2, dtype=int) % P
    for entries in itertools.product(range(P), repeat=4):
        a = np.array(entries, dtype=int).reshape(2, 2) % P
        det = round(np.linalg.det(a)) % P
        if det == 0:
            continue
        if np.array_equal(a.T @ a % P, eye):
            out.append(a)
    assert len(out) == 8
    return out


def adjacency_matrix():
    a = np.zeros((9, 9), dtype=int)
    for p in POINTS:
        for d in NORM_ONE:
            q = ((p[0] + d[0]) % P, (p[1] + d[1]) % P)
            a[INDEX[p], INDEX[q]] = 1
    return a


def permutation_matrix(linear, translation):
    pmat = np.zeros((9, 9), dtype=int)
    for p in POINTS:
        v = np.array(p, dtype=int)
        qv = (linear @ v + np.array(translation, dtype=int)) % P
        q = tuple(int(x) for x in qv)
        pmat[INDEX[q], INDEX[p]] = 1
    return pmat


def verify():
    adjacency = adjacency_matrix()
    degree = int(adjacency.sum(axis=1)[0])
    assert degree == 4
    laplacian = degree * np.eye(9, dtype=int) - adjacency

    linear_parts = orthogonal_linear_parts()
    transformations = [
        permutation_matrix(a, t)
        for a in linear_parts
        for t in POINTS
    ]
    assert len(transformations) == 72

    adjacency_ok = all(np.array_equal(p.T @ adjacency @ p, adjacency) for p in transformations)
    laplacian_ok = all(np.array_equal(p @ laplacian, laplacian @ p) for p in transformations)
    assert adjacency_ok and laplacian_ok

    values = np.linalg.eigvalsh(laplacian.astype(float))
    rounded = [int(round(float(x))) for x in values]
    spectrum = {x: rounded.count(x) for x in sorted(set(rounded))}
    assert spectrum == {0: 1, 3: 4, 6: 4}

    return {
        "vertex_count": 9,
        "degree": degree,
        "affine_orthogonal_action_order": len(transformations),
        "all_affine_orthogonal_actions_preserve_adjacency": adjacency_ok,
        "all_affine_orthogonal_actions_commute_with_laplacian": laplacian_ok,
        "laplacian_spectrum": spectrum,
        "nonzero_spectral_gap": 3,
        "physical_kinetic_coefficient_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
