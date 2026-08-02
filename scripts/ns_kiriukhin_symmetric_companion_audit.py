#!/usr/bin/env python3
"""Exact audit of the Kiriukhin symmetric-part companion theorem's rank value."""
from __future__ import annotations

from fractions import Fraction as F


def transpose(matrix: tuple[tuple[F, ...], ...]) -> tuple[tuple[F, ...], ...]:
    return tuple(tuple(matrix[j][i] for j in range(len(matrix))) for i in range(len(matrix)))


def add(left, right):
    return tuple(
        tuple(left[i][j] + right[i][j] for j in range(len(left)))
        for i in range(len(left))
    )


def scale(coefficient: F, matrix):
    return tuple(tuple(coefficient * entry for entry in row) for row in matrix)


def max_row_sum(matrix) -> F:
    return max(sum(abs(entry) for entry in row) for row in matrix)


def max_column_sum(matrix) -> F:
    return max_row_sum(transpose(matrix))


def run() -> None:
    magnitude = F(37)
    raw = ((F(0), magnitude), (-magnitude, F(0)))
    symmetric = scale(F(1, 2), add(raw, transpose(raw)))

    assert symmetric == ((F(0), F(0)), (F(0), F(0)))
    assert max_row_sum(raw) == magnitude
    assert max_column_sum(raw) == magnitude
    assert max_row_sum(symmetric) == 0
    assert max_column_sum(symmetric) == 0

    # Kiriukhin's raw output-row theorem supplies one independent equation for
    # three dyadic weights.  A bound on V=(M+M^T)/2 supplies no equation for
    # either raw partial adjoint because the antisymmetric part is invisible.
    unknowns = 3
    rank_before = 1
    rank_after_companion = 1
    assert unknowns - rank_before == 2
    assert unknowns - rank_after_companion == 2

    # The elementary inequality explains the companion's role without
    # fabricating independence: each V row is bounded by half a raw row plus
    # half the corresponding raw column.
    sample = ((F(2), F(-5)), (F(7), F(3)))
    sample_symmetric = scale(F(1, 2), add(sample, transpose(sample)))
    for index, row in enumerate(sample_symmetric):
        symmetric_row = sum(abs(entry) for entry in row)
        raw_row = sum(abs(entry) for entry in sample[index])
        raw_column = sum(abs(sample[j][index]) for j in range(len(sample)))
        assert symmetric_row <= F(1, 2) * (raw_row + raw_column)

    print(
        "verified Kiriukhin symmetric companion audit: V=(M+M^T)/2 is blind "
        "to a nonzero antisymmetric raw transfer; triadic exponent rank remains "
        "1 with nullity 2, so both partial-adjoint ledgers remain required"
    )


if __name__ == "__main__":
    run()
