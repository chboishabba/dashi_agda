#!/usr/bin/env python3
"""Finite verification of the concrete C3^2 semidirect C2 permutation spine.

Besides the 9-slot face action, this verifies the actual 3x3 coordinate actor
used by the first-Tits/trinification interpretation.  The cyclic row matrix P
has det(P)=1 over F3.  On a 3x3 matrix X,

    rowShift(X)    = P X,
    columnShift(X) = X P^-1,

so the two cube translations are literal determinant-one left/right matrix
actors of the form used by the SL3^3 action on an M3 sector.

This remains a finite same-action receipt.  It does not identify continuous DHR
or physical gauge semantics, and the 18 permutation elements do not exhaust the
27-dimensional F3-linear centralizer.
"""
from __future__ import annotations

from itertools import product

P = 3
N = 3
DIM = N * N


def index(x: int, y: int) -> int:
    return N * x + y


def identity(n: int = DIM) -> list[list[int]]:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def multiply(a, b) -> list[list[int]]:
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) % P for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def transpose(a):
    return [list(row) for row in zip(*a)]


def determinant3(a) -> int:
    return (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    ) % P


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

# The actual 3x3 determinant-one coordinate cycle.
P3 = [
    [0, 1, 0],
    [0, 0, 1],
    [1, 0, 0],
]
P3_INV = transpose(P3)
I3 = identity(3)


def power(a, exponent: int):
    out = identity(len(a))
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


def table_from_flat(flat):
    return [list(flat[N * i : N * (i + 1)]) for i in range(N)]


def flat_from_table(table):
    return [x for row in table for x in row]


def face_apply(permutation, table):
    flat = flat_from_table(table)
    out = [sum(permutation[i][j] * flat[j] for j in range(DIM)) % P for i in range(DIM)]
    return table_from_flat(out)


def all_tables():
    for flat in product(range(P), repeat=DIM):
        yield table_from_flat(flat)


def receipt() -> dict:
    elements = tuple(product(range(3), range(3), range(2)))
    matrices = {element: action(element) for element in elements}

    faithful = len({freeze(matrix) for matrix in matrices.values()}) == 18
    multiplication_exact = all(
        multiply(matrices[left], matrices[right])
        == matrices[normal_multiply(left, right)]
        for left, right in product(elements, repeat=2)
    )

    # Check the 3x3 same-action formulas exhaustively on all 3^9 M3(F3) tables.
    row_same_action = True
    column_same_action = True
    for table in all_tables():
        if face_apply(ROW, table) != multiply(P3, table):
            row_same_action = False
            break
        if face_apply(COLUMN, table) != multiply(table, P3_INV):
            column_same_action = False
            break

    return {
        "normal_form": "(row mod 3, column mod 3, reflection mod 2)",
        "normal_form_count": len(elements),
        "distinct_permutation_matrices": len({freeze(matrix) for matrix in matrices.values()}),
        "row_order_three": power(ROW, 3) == IDENTITY,
        "column_order_three": power(COLUMN, 3) == IDENTITY,
        "translations_commute": multiply(ROW, COLUMN) == multiply(COLUMN, ROW),
        "transpose_order_two": multiply(TRANSPOSE, TRANSPOSE) == IDENTITY,
        "transpose_row_to_column": multiply(TRANSPOSE, ROW) == multiply(COLUMN, TRANSPOSE),
        "transpose_column_to_row": multiply(TRANSPOSE, COLUMN) == multiply(ROW, TRANSPOSE),
        "faithful_18_state_action": faithful,
        "all_324_products_match_semidirect_law": multiplication_exact,
        "sl3_coordinate_cycle_matrix": P3,
        "sl3_coordinate_cycle_determinant_mod3": determinant3(P3),
        "sl3_coordinate_cycle_order_three": power(P3, 3) == I3,
        "row_shift_equals_left_P_action_on_all_3pow9_tables": row_same_action,
        "column_shift_equals_right_P_inverse_action_on_all_3pow9_tables": column_same_action,
        "interpretation": "faithful C3^2 semidirect C2 permutation spine; the C3^2 translations are literal determinant-one left/right SL3 coordinate-cycle actions on M3(F3)",
        "boundary": "finite same-action only; no continuous DHR/physical gauge promotion",
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
    assert result["sl3_coordinate_cycle_determinant_mod3"] == 1
    assert result["sl3_coordinate_cycle_order_three"]
    assert result["row_shift_equals_left_P_action_on_all_3pow9_tables"]
    assert result["column_shift_equals_right_P_inverse_action_on_all_3pow9_tables"]
    print(result)


if __name__ == "__main__":
    main()
