#!/usr/bin/env python3
"""Finite GF(3) audit of the concrete 3x3 face-operator stabilizer.

Numerical evidence only.  Agda theorem authority remains
IITCubeDiagonalStabilizerExact: diagonal additive graph preservation iff
commutation with the concrete operator B.
"""
from __future__ import annotations

from itertools import product

P = 3
N_SIDE = 3
DIM = N_SIDE * N_SIDE


def index(x: int, y: int) -> int:
    return N_SIDE * x + y


def face_operator() -> list[list[int]]:
    """B = cyclic-row-shift + cyclic-column-shift over F3."""
    out = [[0] * DIM for _ in range(DIM)]
    for x, y in product(range(N_SIDE), repeat=2):
        row = index(x, y)
        out[row][index((x + 1) % N_SIDE, y)] = 1
        j = index(x, (y + 1) % N_SIDE)
        out[row][j] = (out[row][j] + 1) % P
    return out


def identity(n: int) -> list[list[int]]:
    return [[int(i == j) for j in range(n)] for i in range(n)]


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


def rank_mod(a) -> int:
    m = [row[:] for row in a]
    rows = len(m)
    cols = len(m[0]) if rows else 0
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if m[r][col] % P), None)
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        inv = pow(m[rank][col] % P, -1, P)
        m[rank] = [(x * inv) % P for x in m[rank]]
        for r in range(rows):
            if r != rank and m[r][col] % P:
                f = m[r][col] % P
                m[r] = [(x - f * y) % P for x, y in zip(m[r], m[rank])]
        rank += 1
        if rank == rows:
            break
    return rank


def centralizer_equations(b):
    """Linear system for X B - B X = 0 on the 81 entries of X."""
    eqs = []
    for i in range(DIM):
        for j in range(DIM):
            row = [0] * (DIM * DIM)
            for k in range(DIM):
                row[DIM * i + k] = (row[DIM * i + k] + b[k][j]) % P
                row[DIM * k + j] = (row[DIM * k + j] - b[i][k]) % P
            eqs.append(row)
    return eqs


def receipt() -> dict:
    b = face_operator()
    n = add(b, identity(DIM))
    n2 = power(n, 2)
    n3 = power(n, 3)

    rank_n = rank_mod(n)
    rank_n2 = rank_mod(n2)
    rank_n3 = rank_mod(n3)
    kernel_dims = [DIM - rank_n, DIM - rank_n2, DIM - rank_n3]

    eq_rank = rank_mod(centralizer_equations(b))
    centralizer_dim = DIM * DIM - eq_rank

    return {
        "field": "F3",
        "face_dimension": DIM,
        "nilpotent_operator": "N = B + I",
        "rank_N": rank_n,
        "rank_N2": rank_n2,
        "rank_N3": rank_n3,
        "kernel_dimensions": kernel_dims,
        "N3_zero": all(x == 0 for row in n3 for x in row),
        "jordan_block_sizes_for_B": [3, 3, 3],
        "centralizer_equation_rank": eq_rank,
        "centralizer_dimension": centralizer_dim,
        "expected_centralizer_algebra_after_basis_choice": "M3(F3[t]/(t^3))",
        "formal_boundary": "numeric finite-linear-algebra receipt; Agda owns PreservesGraph <-> CommutesWithB",
    }


def main() -> None:
    result = receipt()
    assert result["kernel_dimensions"] == [3, 6, 9]
    assert result["N3_zero"]
    assert result["jordan_block_sizes_for_B"] == [3, 3, 3]
    assert result["centralizer_dimension"] == 27
    print(result)


if __name__ == "__main__":
    main()
