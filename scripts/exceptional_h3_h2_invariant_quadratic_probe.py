#!/usr/bin/env python3
from __future__ import annotations

import itertools
import numpy as np

P = 3
POINTS = tuple(itertools.product(range(P), repeat=2))
INDEX = {p: i for i, p in enumerate(POINTS)}
NORM1 = ((1, 0), (2, 0), (0, 1), (0, 2))


def orthogonal_linear_parts():
    out = []
    eye = np.eye(2, dtype=int) % P
    for entries in itertools.product(range(P), repeat=4):
        a = np.array(entries, dtype=int).reshape(2, 2) % P
        det = int(round(np.linalg.det(a))) % P
        if det != 0 and np.array_equal(a.T @ a % P, eye):
            out.append(a)
    assert len(out) == 8
    return out


def affine_permutations():
    out = []
    for a in orthogonal_linear_parts():
        for t in POINTS:
            perm = []
            for p in POINTS:
                qv = (a @ np.array(p, dtype=int) + np.array(t, dtype=int)) % P
                perm.append(INDEX[tuple(int(x) for x in qv)])
            out.append(tuple(perm))
    assert len(out) == 72
    return out


def pair_orbits(perms):
    remaining = {(i, j) for i in range(9) for j in range(9)}
    orbits = []
    while remaining:
        seed = next(iter(remaining))
        orbit = {(p[seed[0]], p[seed[1]]) for p in perms}
        orbits.append(orbit)
        remaining -= orbit
    return sorted(orbits, key=len)


def adjacency_norm1():
    a = np.zeros((9, 9), dtype=int)
    for p in POINTS:
        for d in NORM1:
            q = ((p[0] + d[0]) % P, (p[1] + d[1]) % P)
            a[INDEX[p], INDEX[q]] = 1
    return a


def verify():
    perms = affine_permutations()
    orbits = pair_orbits(perms)
    sizes = sorted(len(o) for o in orbits)
    assert sizes == [9, 36, 36]

    # A transitive permutation group's invariant kernels are exactly the
    # matrices constant on ordered-pair orbits.  Here those are diagonal,
    # norm-1 displacement and norm-2 displacement.
    invariant_kernel_dimension = len(orbits)
    assert invariant_kernel_dimension == 3

    a1 = adjacency_norm1()
    eye = np.eye(9, dtype=int)
    ones = np.ones((9, 9), dtype=int)
    a2 = ones - eye - a1
    assert np.all(a2.sum(axis=1) == 4)

    # Locality to norm-1 neighbors removes A2.  Requiring K*1=0 then forces
    # K = kappa(4I-A1), a one-dimensional family.
    lap = 4 * eye - a1
    assert np.array_equal(lap @ np.ones(9, dtype=int), np.zeros(9, dtype=int))

    vals = np.linalg.eigvalsh(lap.astype(float))
    rounded = [int(round(float(x))) for x in vals]
    spectrum = {x: rounded.count(x) for x in sorted(set(rounded))}
    assert spectrum == {0: 1, 3: 4, 6: 4}

    return {
        "ordered_pair_orbit_sizes": sizes,
        "invariant_kernel_dimension": invariant_kernel_dimension,
        "invariant_basis": ["I", "A_norm1", "A_norm2"],
        "local_constant_annihilating_family_dimension": 1,
        "canonical_local_operator": "4I-A_norm1",
        "canonical_local_spectrum": spectrum,
        "physical_kinetic_coefficient_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
