#!/usr/bin/env python3
from __future__ import annotations

import itertools
import numpy as np

P = 3
B = np.array([
    [2,2,0,0,0],
    [2,2,2,0,2],
    [0,2,2,2,0],
    [0,0,2,2,0],
    [0,2,0,0,2],
], dtype=int) % P


def canon(v):
    v = tuple(int(x) % P for x in v)
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return tuple(inv * x % P for x in v)
    raise ValueError("zero vector")


def quadratic(v):
    a = np.array(v, dtype=int)
    return int(a @ B @ a) % P


def rref_subspaces(k, n=5):
    for pivots in itertools.combinations(range(n), k):
        base = np.zeros((k, n), dtype=int)
        for i, p in enumerate(pivots):
            base[i, p] = 1
        nonp = [j for j in range(n) if j not in pivots]
        free = [(i, j) for i, p in enumerate(pivots) for j in nonp if j > p]
        for vals in itertools.product(range(P), repeat=len(free)):
            a = base.copy()
            for (i, j), v in zip(free, vals):
                a[i, j] = v
            yield a


def projective_lines(a):
    k = a.shape[0]
    out = set()
    for coeffs in itertools.product(range(P), repeat=k):
        if all(c == 0 for c in coeffs):
            continue
        v = np.zeros(5, dtype=int)
        for i, c in enumerate(coeffs):
            v = (v + c * a[i]) % P
        out.add(canon(v))
    return frozenset(out)


def enumerate_h3_h2():
    points = sorted({canon(v) for v in itertools.product(range(P), repeat=5) if any(v)})
    roots = {p for p in points if quadratic(p) == 2}
    nulls = {p for p in points if quadratic(p) == 0}

    h3 = []
    for a in rref_subspaces(3):
        s = projective_lines(a)
        if sum(p in roots for p in s) == 6 and sum(p in nulls for p in s) == 1:
            h3.append(s)

    h2 = []
    for a in rref_subspaces(2):
        s = projective_lines(a)
        signature = (
            sum(p in roots for p in s),
            sum(p in nulls for p in s),
            sum(quadratic(p) == 1 for p in s),
        )
        if signature == (2, 0, 2):
            h2.append(s)

    assert len(h3) == 120
    assert len(h2) == 270
    return h3, h2


def spectrum_mult(matrix):
    vals = np.linalg.eigvalsh(matrix.astype(float))
    rounded = [int(round(float(x))) for x in vals]
    return {x: rounded.count(x) for x in sorted(set(rounded), reverse=True)}


def verify():
    h3, h2 = enumerate_h3_h2()
    incidence = np.zeros((len(h3), len(h2)), dtype=int)
    for i, h in enumerate(h3):
        for j, face in enumerate(h2):
            if face.issubset(h):
                incidence[i, j] = 1

    assert set(incidence.sum(axis=1).tolist()) == {9}
    assert set(incidence.sum(axis=0).tolist()) == {4}

    gram = incidence @ incidence.T
    adjacency = gram.copy()
    np.fill_diagonal(adjacency, 0)
    assert set(adjacency.sum(axis=1).tolist()) == {27}
    assert np.array_equal(gram, 9 * np.eye(120, dtype=int) + adjacency)

    adj_spec = spectrum_mult(adjacency)
    assert adj_spec == {27: 1, 9: 20, 3: 15, -3: 84}

    laplacian = 27 * np.eye(120, dtype=int) - adjacency
    lap_spec_desc = spectrum_mult(laplacian)
    lap_spec = {x: lap_spec_desc[x] for x in sorted(lap_spec_desc)}
    assert lap_spec == {0: 1, 18: 20, 24: 15, 30: 84}

    return {
        "h3_count": 120,
        "h2_count": 270,
        "incidence_count": int(incidence.sum()),
        "h3_degree": 27,
        "adjacency_spectrum": adj_spec,
        "laplacian_spectrum": lap_spec,
        "base_spectral_gap": 18,
        "incidence_identity_NNt_eq_9I_plus_A": True,
        "physical_base_length_or_time_scale_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
