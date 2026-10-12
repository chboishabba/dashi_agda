#!/usr/bin/env python3
"""Exact finite weld from Monster-3B source compressions to selected GF(729).

PR #1098 derives the literal 6x6 compression matrices below from acquired ATLAS
2.Suz / 2.Suz:2 GF(3)^12 matrices after the unique inner alternating-form
normalization.  This consumer independently checks them against #1105's selected
field

    GF(3)[alpha] / (alpha^6 + alpha^5 + alpha^4 + 1).

Two stages are retained:

* depth 5: beta=1-alpha gives the first exact field-presentation weld, with
  multiplicative order 364;
* depth 7: a stronger source compression has a root gamma in the SAME selected
  field of multiplicative order 728.  Its multiplication action is therefore
  transitive on all 728 nonzero field elements with trivial stabilizer.

Both stages construct explicit invertible Q satisfying Q T = M Q.  The latter
pays the selected finite-field multiplicative action/orbit/stabilizer weld, but
not the broader Monster semantic-action identification or Agda-kernel matrix
certification.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

MOD = 3
DEGREE = 6
SELECTED_MODULUS = (1, 0, 0, 0, 1, 1, 1)  # low -> high
ZERO = (0,) * DEGREE
ONE = (1,) + (0,) * (DEGREE - 1)

BETA_MODULUS = (1, 0, 1, 2, 0, 2, 1)
BETA = (1, 2, 0, 0, 0, 0)  # 1-alpha
BETA_T = (
    (0, 2, 1, 0, 2, 1),
    (2, 0, 2, 1, 2, 2),
    (0, 0, 0, 0, 1, 2),
    (2, 0, 1, 2, 1, 2),
    (2, 0, 2, 2, 0, 2),
    (1, 0, 1, 0, 2, 2),
)

PRIMITIVE_MODULUS = (2, 0, 1, 2, 2, 2, 1)
GAMMA = (0, 2, 0, 1, 2, 0)
PRIMITIVE_T = (
    (0, 0, 0, 2, 2, 2),
    (2, 1, 0, 2, 0, 0),
    (0, 2, 1, 0, 0, 2),
    (1, 0, 1, 0, 2, 0),
    (2, 0, 2, 2, 0, 1),
    (0, 1, 1, 2, 0, 2),
)
PRIMITIVE_SOURCE_WORD = "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"


def trim(poly):
    out = list(poly)
    while len(out) > 1 and out[-1] % MOD == 0:
        out.pop()
    return tuple(x % MOD for x in out)


def poly_add(left, right):
    n = max(len(left), len(right))
    return trim([
        ((left[i] if i < len(left) else 0) +
         (right[i] if i < len(right) else 0)) % MOD
        for i in range(n)
    ])


def poly_mul(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % MOD
    return trim(out)


def poly_scale(poly, scalar):
    return trim([(scalar * x) % MOD for x in poly])


def poly_compose_at_one_minus_x(poly):
    one_minus_x = (1, 2)
    power = (1,)
    out = (0,)
    for coefficient in poly:
        out = poly_add(out, poly_scale(power, coefficient))
        power = poly_mul(power, one_minus_x)
    return trim(out)


def add(a, b):
    return tuple((x + y) % MOD for x, y in zip(a, b))


def scale(a, scalar):
    return tuple((scalar * x) % MOD for x in a)


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
                    coeffs[k - DEGREE + j] - coefficient * modulus_coefficient
                ) % MOD
            coeffs[k] = 0
    return tuple(coeffs[:DEGREE])


def power(a, exponent):
    result = ONE
    base = a
    while exponent:
        if exponent & 1:
            result = mul(result, base)
        base = mul(base, base)
        exponent //= 2
    return result


def multiplicative_order(a):
    if a == ZERO:
        return 0
    current = ONE
    for k in range(1, 3 ** DEGREE):
        current = mul(current, a)
        if current == ONE:
            return k
    raise AssertionError("finite multiplicative order missing")


def eval_poly(coefficients, a):
    result = ZERO
    current = ONE
    for coefficient in coefficients:
        if coefficient:
            result = add(result, scale(current, coefficient))
        current = mul(current, a)
    return result


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
    augmented = [[x % MOD for x in row] + identity(n)[i]
                 for i, row in enumerate(matrix)]
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


def weld(matrix, field_element):
    field_matrix = multiplication_matrix(field_element)
    e0 = [1, 0, 0, 0, 0, 0]
    source_krylov = krylov_matrix(matrix, e0)
    target_krylov = krylov_matrix(field_matrix, e0)
    source_det = determinant_mod3(source_krylov)
    target_det = determinant_mod3(target_krylov)
    Q = matrix_mul(target_krylov, matrix_inverse(source_krylov))
    left = matrix_vec(matrix, swap01(e0))
    right = swap01(matrix_vec(matrix, e0))
    return {
        "multiplication_matrix": field_matrix,
        "cyclic_rank_e0": DEGREE if source_det else 0,
        "field_cyclic_rank_e0": DEGREE if target_det else 0,
        "source_krylov_determinant_mod3": source_det,
        "field_krylov_determinant_mod3": target_det,
        "intertwiner_Q": Q,
        "intertwiner_determinant_mod3": determinant_mod3(Q),
        "intertwining_equation": "Q*T = M*Q",
        "intertwining_verified": matrix_mul(Q, matrix) == matrix_mul(field_matrix, Q),
        "T_swap01_witness": left,
        "swap01_T_witness": right,
        "breaks_swap01_at_e0": left != right,
    }


def build_receipt():
    beta_weld = weld(BETA_T, BETA)
    beta_substitution = poly_compose_at_one_minus_x(SELECTED_MODULUS)
    beta_order = multiplicative_order(BETA)

    primitive_weld = weld(PRIMITIVE_T, GAMMA)
    gamma_order = multiplicative_order(GAMMA)
    gamma_root_verified = eval_poly(PRIMITIVE_MODULUS, GAMMA) == ZERO

    return {
        "schema": "dashi.j369.monster3b.selected_gf729_weld.v2",
        "source_producer": {
            "pr": 1098,
            "branch": "agent/e6-f3-exterior-square-maxcut-20261006",
            "receipt_path": "outputs/monster3b_atlas_compression_field_selector_20261012.json",
        },
        "selected_modulus_low_to_high": list(SELECTED_MODULUS),
        "earlier_beta_weld": {
            "source_word": "g2 g1 g2^-1 g1 g2^-1",
            "compression_modulus_low_to_high": list(BETA_MODULUS),
            "affine_generator_change": "beta = 1 - alpha",
            "beta_coordinates": list(BETA),
            "polynomial_substitution_verified": beta_substitution == BETA_MODULUS,
            "multiplicative_order": beta_order,
            **beta_weld,
        },
        "preferred_primitive_weld": {
            "source_word": PRIMITIVE_SOURCE_WORD,
            "compression_modulus_low_to_high": list(PRIMITIVE_MODULUS),
            "primitive_root_coordinates": list(GAMMA),
            "primitive_root_is_root_of_compression_polynomial": gamma_root_verified,
            "primitive_root_multiplicative_order": gamma_order,
            "compression_matrix": [list(row) for row in PRIMITIVE_T],
            **primitive_weld,
            "punctured_orbit_size": gamma_order,
            "punctured_stabilizer_size": 1 if gamma_order == 728 else 0,
        },
        "selected_field_presentation_weld_paid": (
            beta_substitution == BETA_MODULUS
            and beta_weld["intertwining_verified"]
            and beta_weld["intertwiner_determinant_mod3"] != 0
        ),
        "selected_field_multiplicative_action_weld_paid": (
            gamma_root_verified
            and gamma_order == 728
            and primitive_weld["intertwining_verified"]
            and primitive_weld["intertwiner_determinant_mod3"] != 0
            and primitive_weld["cyclic_rank_e0"] == 6
            and primitive_weld["breaks_swap01_at_e0"]
        ),
        "full_monster_semantic_action_recognition_paid": False,
        "boundary": (
            "The preferred source compression is explicitly conjugate to multiplication "
            "by a primitive element of the already-selected GF(729). Hence its powers "
            "give one 728-element orbit on the punctured field and trivial stabilizer. "
            "This does not by itself identify the broader Monster semantic action or "
            "constitute an Agda-kernel matrix proof."
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
