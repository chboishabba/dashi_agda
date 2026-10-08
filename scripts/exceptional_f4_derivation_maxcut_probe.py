from __future__ import annotations

from collections import Counter
import numpy as np
import sympy as sp

P = 3
INV2 = 2
I3 = np.eye(3, dtype=int) % P


def tr3(a):
    return int(np.trace(a) % P)


def bullet3(a, b):
    return INV2 * (a @ b + b @ a) % P


def bar3(a):
    return INV2 * (tr3(a) * I3 - a) % P


def cross3(a, b):
    """First-Tits x cross y = 1/2 of the bilinearized adjoint."""
    ab = bullet3(a, b)
    return (
        ab
        - INV2 * tr3(a) * b
        - INV2 * tr3(b) * a
        + INV2 * (tr3(a) * tr3(b) - tr3(ab)) * I3
    ) % P


def jprod3(x, y):
    """Standard first-Tits J(M3(F3),1) product."""
    a, b, c = x
    d, e, f = y
    return (
        (bullet3(a, d) + bar3(b @ f) + bar3(e @ c)) % P,
        (bar3(a) @ e + bar3(d) @ b + cross3(c, f)) % P,
        (f @ bar3(a) + c @ bar3(d) + cross3(b, e)) % P,
    )


def basis_element(sector, row, column):
    out = [np.zeros((3, 3), dtype=int) for _ in range(3)]
    out[sector][row, column] = 1
    return tuple(out)


BASIS = [
    basis_element(s, i, j)
    for s in range(3)
    for i in range(3)
    for j in range(3)
]
UNIT = (I3.copy(), np.zeros((3, 3), dtype=int), np.zeros((3, 3), dtype=int))


def flatten(x):
    return np.concatenate([a.reshape(-1) for a in x]) % P


def same(x, y):
    return all(np.array_equal(a % P, b % P) for a, b in zip(x, y))


def add(x, y):
    return tuple((a + b) % P for a, b in zip(x, y))


def sub(x, y):
    return tuple((a - b) % P for a, b in zip(x, y))


def jordan_identity(x, y):
    xx = jprod3(x, x)
    return same(jprod3(jprod3(xx, y), x), jprod3(xx, jprod3(y, x)))


def rank_mod3(matrix):
    a = np.asarray(matrix, dtype=np.int8).copy() % P
    m, n = a.shape
    rank = 0
    for col in range(n):
        pivots = np.flatnonzero(a[rank:, col])
        if pivots.size == 0:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            a[[rank, pivot]] = a[[pivot, rank]]
        if a[rank, col] == 2:
            a[rank] = (2 * a[rank]) % P
        nz = np.flatnonzero(a[rank + 1 :, col])
        if nz.size:
            rows = nz + rank + 1
            factors = a[rows, col].copy()
            a[rows] = (a[rows] - factors[:, None] * a[rank]) % P
        rank += 1
        if rank == m:
            break
    return rank


def independent_indices_mod3(matrix):
    a = np.asarray(matrix, dtype=np.int8).copy() % P
    m, n = a.shape
    labels = list(range(m))
    out = []
    rank = 0
    for col in range(n):
        pivots = np.flatnonzero(a[rank:, col])
        if pivots.size == 0:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            a[[rank, pivot]] = a[[pivot, rank]]
            labels[rank], labels[pivot] = labels[pivot], labels[rank]
        out.append(labels[rank])
        if a[rank, col] == 2:
            a[rank] = (2 * a[rank]) % P
        nz = np.flatnonzero(a[rank + 1 :, col])
        if nz.size:
            rows = nz + rank + 1
            factors = a[rows, col].copy()
            a[rows] = (a[rows] - factors[:, None] * a[rank]) % P
        rank += 1
        if rank == m:
            break
    return out


def structure_constants():
    c = np.zeros((27, 27, 27), dtype=np.int8)
    support = Counter()
    for i, x in enumerate(BASIS):
        for j, y in enumerate(BASIS):
            v = flatten(jprod3(x, y))
            c[:, i, j] = v
            support[int(np.count_nonzero(v))] += 1
    return c, support


def derivation_constraint_matrix(c):
    rows = []
    for i in range(27):
        for j in range(i, 27):
            product_support = np.flatnonzero(c[:, i, j])
            for k in range(27):
                row = np.zeros(729, dtype=np.int8)
                for l in product_support:
                    row[k * 27 + l] = (row[k * 27 + l] + c[l, i, j]) % P
                for p in np.flatnonzero(c[k, :, j]):
                    row[p * 27 + i] = (row[p * 27 + i] - c[k, p, j]) % P
                for q in np.flatnonzero(c[k, i, :]):
                    row[q * 27 + j] = (row[q * 27 + j] - c[k, i, q]) % P
                if np.any(row):
                    rows.append(row)
    return np.asarray(rows, dtype=np.int8) % P


def inner_derivation(x, y, z):
    return sub(jprod3(x, jprod3(y, z)), jprod3(y, jprod3(x, z)))


def inner_derivation_matrices():
    out = []
    for i in range(27):
        for j in range(i + 1, 27):
            d = np.zeros((27, 27), dtype=np.int8)
            for k in range(27):
                d[:, k] = flatten(inner_derivation(BASIS[i], BASIS[j], BASIS[k]))
            if np.any(d):
                out.append(d % P)
    return out


def rational_trace_form():
    half = sp.Rational(1, 2)
    identity = sp.eye(3)

    def tr(a):
        return sp.trace(a)

    def bullet(a, b):
        return half * (a * b + b * a)

    def bar(a):
        return half * (tr(a) * identity - a)

    def cross(a, b):
        ab = bullet(a, b)
        return (
            ab
            - half * tr(a) * b
            - half * tr(b) * a
            + half * (tr(a) * tr(b) - tr(ab)) * identity
        )

    def product(x, y):
        a, b, c = x
        d, e, f = y
        return (
            bullet(a, d) + bar(b * f) + bar(e * c),
            bar(a) * e + bar(d) * b + cross(c, f),
            f * bar(a) + c * bar(d) + cross(b, e),
        )

    basis = []
    for s in range(3):
        for i in range(3):
            for j in range(3):
                mats = [sp.zeros(3) for _ in range(3)]
                mats[s][i, j] = 1
                basis.append(tuple(mats))

    gram = sp.Matrix(
        27,
        27,
        lambda i, j: sp.trace(product(basis[i], basis[j])[0]),
    )
    witness_a = sp.zeros(3)
    witness_a[0, 1] = 1
    witness_a[1, 0] = -1
    witness = (witness_a, sp.zeros(3), sp.zeros(3))
    witness_square_trace = sp.trace(product(witness, witness)[0])
    return gram, witness_square_trace


def verify(seed=369):
    rng = np.random.default_rng(seed)
    assert all(same(jprod3(UNIT, b), b) and same(jprod3(b, UNIT), b) for b in BASIS)
    assert all(jordan_identity(a, b) for a in BASIS for b in BASIS)
    for _ in range(1000):
        x = tuple(rng.integers(0, 3, size=(3, 3), dtype=int) for _ in range(3))
        y = tuple(rng.integers(0, 3, size=(3, 3), dtype=int) for _ in range(3))
        assert jordan_identity(x, y)

    c, support = structure_constants()
    assert support == Counter({0: 414, 1: 291, 2: 24})

    constraints = derivation_constraint_matrix(c)
    constraint_rank = rank_mod3(constraints)
    derivation_dimension = 729 - constraint_rank
    assert constraint_rank == 677
    assert derivation_dimension == 52

    inner = inner_derivation_matrices()
    inner_flat = np.asarray([d.reshape(-1) for d in inner], dtype=np.int8)
    inner_span = rank_mod3(inner_flat)
    assert inner_span == 52

    chosen = independent_indices_mod3(inner_flat)
    derivation_basis = [inner[i] for i in chosen]
    assert len(derivation_basis) == 52

    brackets = []
    for i in range(52):
        for j in range(i + 1, 52):
            brackets.append(
                ((derivation_basis[i] @ derivation_basis[j]
                  - derivation_basis[j] @ derivation_basis[i]) % P).reshape(-1)
            )
    derived_span = rank_mod3(np.asarray(brackets, dtype=np.int8))
    assert derived_span == 52

    centre_constraints = np.zeros((52 * 729, 52), dtype=np.int8)
    for j in range(52):
        for i in range(52):
            bracket = (
                derivation_basis[i] @ derivation_basis[j]
                - derivation_basis[j] @ derivation_basis[i]
            ) % P
            centre_constraints[j * 729 : (j + 1) * 729, i] = bracket.reshape(-1)
    centre_dimension = 52 - rank_mod3(centre_constraints)
    assert centre_dimension == 0

    fixed_constraints = np.vstack(derivation_basis) % P
    common_fixed_dimension = 27 - rank_mod3(fixed_constraints)
    assert common_fixed_dimension == 1

    gram, negative_witness = rational_trace_form()
    assert gram.det() == 1
    assert gram.eigenvals() == {sp.Integer(1): 15, sp.Integer(-1): 12}
    assert negative_witness == -2

    # The repository rational octonion Albert has
    # tr(X∘X)=a²+b²+c²+2(n(x)+n(y)+n(z)), a positive sum of rational squares.
    # Therefore its trace-square form has signature (27,0), while the rational
    # first-Tits M3^3 form has signature (15,12).  A trace-preserving Jordan
    # intertwiner between these two concrete rational forms is impossible.

    return {
        "constraint_rank": constraint_rank,
        "derivation_dimension": derivation_dimension,
        "inner_derivation_span": inner_span,
        "derived_lie_span": derived_span,
        "derivation_centre_dimension": centre_dimension,
        "common_fixed_dimension": common_fixed_dimension,
        "first_tits_trace_signature": (15, 12),
        "compact_albert_trace_signature": (27, 0),
        "negative_trace_square_witness": negative_witness,
        "basis_pair_support": dict(support),
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
