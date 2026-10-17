#!/usr/bin/env python3
"""Finite verification of the concrete C3^2 semidirect C2 permutation spine.

This is a numerical/combinatorial receipt for
DASHI.Biology.IITCubePermutationStabilizer18Exact.  It verifies on the actual
3x3 face coordinates that the row and column order-three translations together
with transpose give 18 distinct permutation matrices and obey the expected
semidirect-product multiplication law.

It does not claim these 18 permutations exhaust the full F3-linear centralizer;
the independent stabilizer scan gives that algebra dimension 27.
"""
from __future__ import annotations

from itertools import product

N = 3
DIM = N * N


def index(x: int, y: int) -> int:
    return N * x + y


def identity() -> list[list[int]]:
    return [[int(i == j) for j in range(DIM)] for i in range(DIM)]


def multiply(a, b) -> list[list[int]]:
    return [
        [sum(a[i][k] * b[k][j] for k in range(DIM)) % 3 for j in range(DIM)]
        for i in range(DIM)
    ]


def permutation_matrix(source_for_output) -> list[list[int]]:
    out = [[0] * DIM for _ in range(DIM)]
    for x, y in product(range(N), repeat=2):
        sx, sy = source_for_output(x, y)
        out[index(x, y)][index(sx, sy)] = 1
    return out


ROW = permutation_matrix(lambda x, y: ((x + 1) % N, y))
COLUMN = permutation_matrix(lambda x, y: (x, (y + 1) % N))
TRANSPOSE = permutation_matrix(lambda x, y: (y, x))
IDENTITY = identity()


def power(a, exponent: int) -> list[list[int]]:
    out = IDENTITY
    for _ in range(exponent):
        out = multiply(out, a)
    return out


def action(element: tuple[int, int, int]) -> list[list[int]]:
    row, column, reflection = element
    return multiply(
        multiply(power(ROW, row), power(COLUMN, column)),
        TRANSPOSE if reflection else IDENTITY,
    )


def normal_multiply(
    left: tuple[int, int, int], right: tuple[int, int, int]
) -> tuple[int, int, int]:
    a, b, reflection = left
    c, d, other_reflection = right
    if reflection:
        c, d = d, c
    return ((a + c) % 3, (b + d) % 3, reflection ^ other_reflection)


def freeze(matrix) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(row) for row in matrix)


def receipt() -> dict:
    elements = tuple(product(range(3), range(3), range(2)))
    matrices = {element: action(element) for element in elements}

    faithful = len({freeze(matrix) for matrix in matrices.values()}) == 18
    multiplication_exact = all(
        multiply(matrices[left], matrices[right])
        == matrices[normal_multiply(left, right)]
        for left, right in product(elements, repeat=2)
    )

    return {
        "normal_form": "(row mod 3, column mod 3, reflection mod 2)",
        "normal_form_count": len(elements),
        "distinct_permutation_matrices": len(
            {freeze(matrix) for matrix in matrices.values()}
        ),
        "row_order_three": power(ROW, 3) == IDENTITY,
        "column_order_three": power(COLUMN, 3) == IDENTITY,
        "translations_commute": multiply(ROW, COLUMN) == multiply(COLUMN, ROW),
        "transpose_order_two": multiply(TRANSPOSE, TRANSPOSE) == IDENTITY,
        "transpose_row_to_column": multiply(TRANSPOSE, ROW)
        == multiply(COLUMN, TRANSPOSE),
        "transpose_column_to_row": multiply(TRANSPOSE, COLUMN)
        == multiply(ROW, TRANSPOSE),
        "faithful_18_state_action": faithful,
        "all_324_products_match_semidirect_law": multiplication_exact,
        "interpretation": "faithful C3^2 semidirect C2 permutation spine inside the larger F3-linear centralizer",
    }


def main() -> None:
    result = receipt()
    assert result["normal_form_count"] == 18
    assert result["distinct_permutation_matrices"] == 18
    assert result["row_order_three"]
    assert result["column_order_three"]
    assert result["translations_commute"]
    assert result["transpose_order_two"]
    assert result["transpose_row_to_column"]
    assert result["transpose_column_to_row"]
    assert result["faithful_18_state_action"]
    assert result["all_324_products_match_semidirect_law"]
    print(result)


if __name__ == "__main__":
    main()
