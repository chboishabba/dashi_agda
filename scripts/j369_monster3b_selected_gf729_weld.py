#!/usr/bin/env python3
"""Exact finite weld from the Monster-3B compression to selected GF(729).

Producer provenance:
  PR #1098 / Monster3B ATLAS compression receipt derives the 6x6 matrix below
  from the acquired ATLAS 2.Suz / 2.Suz:2 GF(3)^12 matrices after the unique
  inner alternating-form normalization.  Its source word is

      g2 g1 g2^-1 g1 g2^-1.

This consumer does not reassert the Monster source derivation.  It independently
checks the remaining J369 finite-field presentation gap against #1105's selected
model

    GF(3)[alpha] / (alpha^6 + alpha^5 + alpha^4 + 1).

The compression polynomial is exactly obtained by beta = 1-alpha:

    f(1-x) = x^6 - x^5 - x^3 + x^2 + 1  (mod 3).

We then construct multiplication-by-beta on the selected polynomial basis and
an explicit invertible Q satisfying

    Q T = M_beta Q.

That pays the finite selected-field presentation weld.  It still does not pay
the larger Monster action/orbit/stabilizer semantic recognition contract.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

MOD = 3
DEGREE = 6

SELECTED_MODULUS = (1, 0, 0, 0, 1, 1, 1)  # low -> high
COMPRESSION_MODULUS = (1, 0, 1, 2, 0, 2, 1)
BETA = (1, 2, 0, 0, 0, 0)  # 1 - alpha

COMPRESSION_MATRIX = (
    (0, 2, 1, 0, 2, 1),
    (2, 0, 2, 1, 2, 2),
    (0, 0, 0, 0, 1, 2),
    (2, 0, 1, 2, 1, 2),
    (2, 0, 2, 2, 0, 2),
    (1, 0, 1, 0, 2, 2),
)


def trim(poly):
    out = list(poly)
    while len(out) > 1 and out[-1] % MOD == 0:
        out.pop()
    return tuple(x % MOD for x in out)


def poly_add(left, right):
    n = max(len(left), len(right))
    out = [0] * n
    for i in range(n):
        out[i] = ((left[i] if i < len(left) else 0)
                  + (right[i] if i < len(right) else 0)) % MOD
    return trim(out)


def poly_mul(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % MOD
    return trim(out)


def poly_scale(poly, scalar):
    return trim([(scalar * x) % MOD for x in poly])


def poly_compose_at_one_minus_x(poly):
    """Return poly(1-x) over GF(3), coefficients low -> high."""
    one_minus_x = (1, 2)
    power = (1,)
    out = (0,)
    for coefficient in poly:
        out = poly_add(out, poly_scale(power, coefficient))
        power = poly_mul(power, one_minus_x)
    return trim(out)


def add(a, b):
    return tuple((x + y) % MOD for x, y in zip(a, b))


def mul(a, b):
    coeffs = [0] * (2 * DEGREE - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            coeffs[i + j] = (coeffs[i + j] + x * y) % MOD
    lower = SELECTED_MODULUS[:-1]
    for k in range(2 * DEGREE - 2, DEGREE - 1, -1):
        coefficient = coeffs[k] % MOD
        if coefficient:
            for j, modulus_coefficient in enumerate(lower):
                coeffs[k - DEGREE + j] = (
                    coeffs[k - DEGREE + j]
                    - coefficient * modulus_coefficient
                ) % MOD
            coeffs[k] = 0
    return tuple(coeffs[:DEGREE])


def matrix_mul(left, right):
    return [
        [sum(left[i][k] * right[k][j] for k in range(len(right))) % MOD
         for j in range(len(right[0]))]
        for i in range(len(left))
    ]


def matrix_vec(matrix, vector):
    return [sum(a * b for a, b in zip(row, vector)) % MOD for row in matrix]


def identity(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def matrix_inverse(matrix):
    n = len(matrix)
    augmented = [
        [x % MOD for x in row] + identity(n)[i]
        for i, row in enumerate(matrix)
    ]
    for column in range(n):
        pivot = next(i for i in range(column, n) if augmented[i][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        inverse = 1 if augmented[column][column] == 1 else 2
        augmented[column] = [(inverse * x) % MOD for x in augmented[column]]
        for row in range(n):
            if row != column and augmented[row][column]:
                coefficient = augmented[row][column]
                augmented[row] = [
                    (x - coefficient * y) % MOD
                    for x, y in zip(augmented[row], augmented[column])
                ]
    return [row[n:] for row in augmented]


def determinant_mod3(matrix):
    work = [[x % MOD for x in row] for row in matrix]
    determinant = 1
    n = len(work)
    for column in range(n):
        pivot = next((i for i in range(column, n) if work[i][column]), None)
        if pivot is None:
            return 0
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            determinant = (-determinant) % MOD
        pivot_value = work[column][column]
        determinant = determinant * pivot_value % MOD
        inverse = 1 if pivot_value == 1 else 2
        work[column] = [(inverse * x) % MOD for x in work[column]]
        for row in range(column + 1, n):
            if work[row][column]:
                coefficient = work[row][column]
                work[row] = [
                    (x - coefficient * y) % MOD
                    for x, y in zip(work[row], work[column])
                ]
    return determinant


def multiplication_matrix(element):
    columns = []
    for j in range(DEGREE):
        basis = tuple(1 if i == j else 0 for i in range(DEGREE))
        columns.append(mul(element, basis))
    return [[columns[j][i] for j in range(DEGREE)] for i in range(DEGREE)]


def krylov_matrix(matrix, vector):
    columns = []
    current = list(vector)
    for _ in range(DEGREE):
        columns.append(current)
        current = matrix_vec(matrix, current)
    return [[columns[j][i] for j in range(DEGREE)] for i in range(DEGREE)]


def swap01(vector):
    out = list(vector)
    out[0], out[1] = out[1], out[0]
    return out


def build_receipt():
    substituted = poly_compose_at_one_minus_x(SELECTED_MODULUS)
    polynomial_substitution_verified = substituted == COMPRESSION_MODULUS

    beta_matrix = multiplication_matrix(BETA)
    e0 = [1, 0, 0, 0, 0, 0]
    compression_krylov = krylov_matrix(COMPRESSION_MATRIX, e0)
    selected_krylov = krylov_matrix(beta_matrix, e0)
    compression_krylov_det = determinant_mod3(compression_krylov)
    selected_krylov_det = determinant_mod3(selected_krylov)

    Q = matrix_mul(selected_krylov, matrix_inverse(compression_krylov))
    intertwining_verified = (
        matrix_mul(Q, COMPRESSION_MATRIX)
        == matrix_mul(beta_matrix, Q)
    )

    left = matrix_vec(COMPRESSION_MATRIX, swap01(e0))
    right = swap01(matrix_vec(COMPRESSION_MATRIX, e0))

    return {
        "schema": "dashi.j369.monster3b.selected_gf729_weld.v1",
        "source_producer": {
            "pr": 1098,
            "branch": "agent/e6-f3-exterior-square-maxcut-20261006",
            "receipt_path": "outputs/monster3b_atlas_compression_field_selector_20261012.json",
            "source_word": "g2 g1 g2^-1 g1 g2^-1",
        },
        "selected_modulus_low_to_high": list(SELECTED_MODULUS),
        "compression_modulus_low_to_high": list(COMPRESSION_MODULUS),
        "affine_generator_change": "beta = 1 - alpha",
        "beta_coordinates": list(BETA),
        "polynomial_substitution_verified": polynomial_substitution_verified,
        "compression_matrix": [list(row) for row in COMPRESSION_MATRIX],
        "multiplication_by_beta_matrix": beta_matrix,
        "cyclic_rank_e0": DEGREE if compression_krylov_det else 0,
        "selected_beta_cyclic_rank_e0": DEGREE if selected_krylov_det else 0,
        "compression_krylov_determinant_mod3": compression_krylov_det,
        "selected_beta_krylov_determinant_mod3": selected_krylov_det,
        "intertwiner_Q": Q,
        "intertwiner_determinant_mod3": determinant_mod3(Q),
        "intertwining_equation": "Q*T = M_beta*Q",
        "intertwining_verified": intertwining_verified,
        "swap01_witness": e0,
        "T_swap01_witness": left,
        "swap01_T_witness": right,
        "breaks_swap01_at_e0": left != right,
        "selected_field_presentation_weld_paid": (
            polynomial_substitution_verified
            and compression_krylov_det != 0
            and selected_krylov_det != 0
            and determinant_mod3(Q) != 0
            and intertwining_verified
            and left != right
        ),
        "full_action_orbit_stabilizer_recognition_paid": False,
        "boundary": (
            "This exact finite computation identifies the source compression with "
            "multiplication by beta=1-alpha in the already-selected GF(729) presentation. "
            "It does not by itself identify all downstream Monster action/orbit/stabilizer "
            "semantics or constitute an Agda-kernel matrix proof."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    receipt = build_receipt()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
