#!/usr/bin/env python3
"""Finite GF(3) audit of the concrete 3x3 face-operator stabilizer.

Numerical evidence only.  Agda theorem authority remains
IITCubeDiagonalStabilizerExact: diagonal additive graph preservation iff
commutation with the concrete operator B.

This scan goes beyond dimension counting.  It constructs an explicit Jordan
chain basis for N=B+I, verifies three size-3 Jordan blocks, constructs 27
commuting basis endomorphisms, and checks their full multiplication table is
that of M_3(F_3[t]/(t^3)) in the chosen basis.
"""
from __future__ import annotations

from itertools import product

P = 3
N_SIDE = 3
DIM = N_SIDE * N_SIDE


def index(x: int, y: int) -> int:
    return N_SIDE * x + y


def identity(n: int) -> list[list[int]]:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def zero_matrix(m: int, n: int) -> list[list[int]]:
    return [[0] * n for _ in range(m)]


def face_operator() -> list[list[int]]:
    """B = cyclic-row-shift + cyclic-column-shift over F3."""
    out = zero_matrix(DIM, DIM)
    for x, y in product(range(N_SIDE), repeat=2):
        row = index(x, y)
        out[row][index((x + 1) % N_SIDE, y)] = 1
        j = index(x, (y + 1) % N_SIDE)
        out[row][j] = (out[row][j] + 1) % P
    return out


def add(a, b):
    return [[(x + y) % P for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def mul(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) % P for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def power(a, k: int):
    out = identity(len(a))
    for _ in range(k):
        out = mul(out, a)
    return out


def rref_mod(a):
    m = [row[:] for row in a]
    rows = len(m)
    cols = len(m[0]) if rows else 0
    rank = 0
    pivots = []
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if m[r][col] % P), None)
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        inv = pow(m[rank][col] % P, -1, P)
        m[rank] = [(x * inv) % P for x in m[rank]]
        for r in range(rows):
            if r != rank and m[r][col] % P:
                factor = m[r][col] % P
                m[r] = [(x - factor * y) % P for x, y in zip(m[r], m[rank])]
        pivots.append(col)
        rank += 1
        if rank == rows:
            break
    return m, pivots


def rank_mod(a) -> int:
    return len(rref_mod(a)[1])


def inverse_mod(a):
    n = len(a)
    augmented = [row[:] + eye for row, eye in zip(a, identity(n))]
    rank = 0
    for col in range(n):
        pivot = next((r for r in range(rank, n) if augmented[r][col] % P), None)
        if pivot is None:
            raise ValueError("singular matrix")
        augmented[rank], augmented[pivot] = augmented[pivot], augmented[rank]
        inv = pow(augmented[rank][col] % P, -1, P)
        augmented[rank] = [(x * inv) % P for x in augmented[rank]]
        for r in range(n):
            if r != rank and augmented[r][col] % P:
                factor = augmented[r][col] % P
                augmented[r] = [
                    (x - factor * y) % P
                    for x, y in zip(augmented[r], augmented[rank])
                ]
        rank += 1
    return [row[n:] for row in augmented]


def transpose(a):
    return [list(col) for col in zip(*a)]


def column(a, j: int):
    return [row[j] for row in a]


def mat_from_columns(columns):
    return transpose(columns)


def flatten(a):
    return [x for row in a for x in row]


def centralizer_equations(b):
    """Linear system for X B - B X = 0 on the 81 entries of X."""
    equations = []
    for i in range(DIM):
        for j in range(DIM):
            row = [0] * (DIM * DIM)
            for k in range(DIM):
                row[DIM * i + k] = (row[DIM * i + k] + b[k][j]) % P
                row[DIM * k + j] = (row[DIM * k + j] - b[i][k]) % P
            equations.append(row)
    return equations


def jordan_chain_basis(n):
    """Columns [N^2 e_i, N e_i, e_i] for i=0,1,2."""
    n2 = power(n, 2)
    eye = identity(DIM)
    columns = []
    for i in range(3):
        v = column(eye, i)
        nv = [sum(n[r][c] * v[c] for c in range(DIM)) % P for r in range(DIM)]
        n2v = [sum(n2[r][c] * v[c] for c in range(DIM)) % P for r in range(DIM)]
        columns.extend([n2v, nv, v])
    return mat_from_columns(columns)


def expected_jordan_form():
    out = zero_matrix(DIM, DIM)
    for block in range(3):
        base = 3 * block
        for i in range(3):
            out[base + i][base + i] = 2  # eigenvalue -1 in F3
        out[base][base + 1] = 1
        out[base + 1][base + 2] = 1
    return out


def u3_power(k: int):
    u = [[0, 1, 0], [0, 0, 1], [0, 0, 0]]
    return power(u, k)


def block_basis_element(a: int, b: int, k: int):
    """E_ab tensor t^k in M3(F3[t]/(t^3))."""
    out = zero_matrix(DIM, DIM)
    q = u3_power(k)
    for i in range(3):
        for j in range(3):
            out[3 * a + i][3 * b + j] = q[i][j]
    return out


def centralizer_basis_jordan():
    return {
        (a, b, k): block_basis_element(a, b, k)
        for a, b, k in product(range(3), repeat=3)
    }


def verify_matrix_truncated_polynomial_algebra(basis) -> bool:
    zero = zero_matrix(DIM, DIM)
    for (a, b, k), x in basis.items():
        for (c, d, ell), y in basis.items():
            actual = mul(x, y)
            expected = basis[(a, d, k + ell)] if b == c and k + ell < 3 else zero
            if actual != expected:
                return False
    return True


def receipt() -> dict:
    b = face_operator()
    n = add(b, identity(DIM))
    n2 = power(n, 2)
    n3 = power(n, 3)

    pmat = jordan_chain_basis(n)
    pinv = inverse_mod(pmat)
    jordan = mul(mul(pinv, b), pmat)

    basis_jordan = centralizer_basis_jordan()
    basis_original = [mul(mul(pmat, x), pinv) for x in basis_jordan.values()]

    equation_rank = rank_mod(centralizer_equations(b))
    centralizer_dimension = DIM * DIM - equation_rank
    explicit_basis_rank = rank_mod([flatten(x) for x in basis_original])
    explicit_basis_all_commute = all(mul(x, b) == mul(b, x) for x in basis_original)

    return {
        "field": "F3",
        "face_dimension": DIM,
        "nilpotent_operator": "N = B + I",
        "rank_N": rank_mod(n),
        "rank_N2": rank_mod(n2),
        "rank_N3": rank_mod(n3),
        "kernel_dimensions": [DIM - rank_mod(n), DIM - rank_mod(n2), DIM - rank_mod(n3)],
        "N3_zero": all(x == 0 for row in n3 for x in row),
        "jordan_chain_basis_rank": rank_mod(pmat),
        "jordan_form_verified": jordan == expected_jordan_form(),
        "jordan_block_sizes_for_B": [3, 3, 3],
        "centralizer_equation_rank": equation_rank,
        "centralizer_dimension": centralizer_dimension,
        "explicit_centralizer_basis_size": len(basis_original),
        "explicit_centralizer_basis_rank": explicit_basis_rank,
        "explicit_basis_all_commute": explicit_basis_all_commute,
        "matrix_truncated_polynomial_multiplication_verified":
            verify_matrix_truncated_polynomial_algebra(basis_jordan),
        "centralizer_algebra_in_chosen_basis": "M3(F3[t]/(t^3))",
        "formal_boundary":
            "numeric finite-linear-algebra receipt; Agda owns PreservesGraph <-> CommutesWithB",
    }


def main() -> None:
    result = receipt()
    assert result["kernel_dimensions"] == [3, 6, 9]
    assert result["N3_zero"]
    assert result["jordan_chain_basis_rank"] == 9
    assert result["jordan_form_verified"]
    assert result["jordan_block_sizes_for_B"] == [3, 3, 3]
    assert result["centralizer_dimension"] == 27
    assert result["explicit_centralizer_basis_size"] == 27
    assert result["explicit_centralizer_basis_rank"] == 27
    assert result["explicit_basis_all_commute"]
    assert result["matrix_truncated_polynomial_multiplication_verified"]
    print(result)


if __name__ == "__main__":
    main()
