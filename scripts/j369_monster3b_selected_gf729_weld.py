#!/usr/bin/env python3
"""Exact finite weld from Monster-3B source compressions to selected GF(729).

PR #1098 derives literal 6x6 X6-compression matrices from acquired ATLAS
2.Suz / 2.Suz:2 GF(3)^12 matrices after the unique inner alternating-form
normalization.  This consumer checks those source-derived operators against
#1105's already-selected field

    GF(3)[alpha] / (alpha^6 + alpha^5 + alpha^4 + 1).

Three receipts are deliberately kept separate:

* depth 5, multiplier 1: beta=1-alpha, order 364; this first paid the selected
  field-presentation seam and has an exact selected-word Heisenberg lift;
* depth 7, multiplier 2: primitive order 728; useful full-normalizer comparator
  whose center-scaled lift exchanges the nontrivial central-character sectors;
* depth 8, multiplier 1: primitive order 728; preferred same-phase target.  It
  simultaneously supplies the full punctured GF(729) cyclic action and a
  center-preserving Heisenberg lift.

Every selected-field weld constructs an explicit invertible Q with Q*T=M*Q.
This closes the finite field/action presentation, not the larger same-object
Monster phase-resolved state or Fin-90 multiplicity recognition.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

MOD = 3
DEGREE = 6
SELECTED_MODULUS = (1, 0, 0, 0, 1, 1, 1)
ZERO = (0,) * DEGREE
ONE = (1,) + (0,) * (DEGREE - 1)

# Depth-five strict-symplectic field-algebra weld.
BETA_MODULUS = (1, 0, 1, 2, 0, 2, 1)
BETA = (1, 2, 0, 0, 0, 0)
BETA_T = (
    (0, 2, 1, 0, 2, 1),
    (2, 0, 2, 1, 2, 2),
    (0, 0, 0, 0, 1, 2),
    (2, 0, 1, 2, 1, 2),
    (2, 0, 2, 2, 0, 2),
    (1, 0, 1, 0, 2, 2),
)

# Depth-seven primitive center-inverting comparator.
INVERTER_MODULUS = (2, 0, 1, 2, 2, 2, 1)
INVERTER_GAMMA = (0, 2, 0, 1, 2, 0)
INVERTER_T = (
    (0, 0, 0, 2, 2, 2),
    (2, 1, 0, 2, 0, 0),
    (0, 2, 1, 0, 0, 2),
    (1, 0, 1, 0, 2, 0),
    (2, 0, 2, 2, 0, 1),
    (0, 1, 1, 2, 0, 2),
)
INVERTER_SOURCE_WORD = "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"

# Depth-eight primitive center-preserving preferred target.
CENTER_MODULUS = (2, 2, 1, 0, 2, 0, 1)
CENTER_GAMMA = (0, 1, 0, 1, 1, 0)
CENTER_T = (
    (2, 2, 0, 1, 1, 2),
    (0, 0, 0, 1, 1, 2),
    (2, 1, 0, 0, 0, 0),
    (1, 2, 0, 2, 2, 2),
    (0, 0, 1, 1, 1, 2),
    (0, 0, 1, 2, 1, 1),
)
CENTER_SOURCE_WORD = "g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1"


def trim(poly):
    out = list(poly)
    while len(out) > 1 and out[-1] % MOD == 0:
        out.pop()
    return tuple(x % MOD for x in out)


def poly_add(left, right):
    n = max(len(left), len(right))
    return trim([
        ((left[i] if i < len(left) else 0)
         + (right[i] if i < len(right) else 0)) % MOD
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
                    coeffs[k - DEGREE + j]
                    - coefficient * modulus_coefficient
                ) % MOD
            coeffs[k] = 0
    return tuple(coeffs[:DEGREE])


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
    return [[sum(left[i][k] * right[k][j] for k in range(len(right))) % MOD
             for j in range(len(right[0]))]
            for i in range(len(left))]


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


def primitive_receipt(word, multiplier, modulus, field_element, matrix):
    welded = weld(matrix, field_element)
    order = multiplicative_order(field_element)
    root_verified = eval_poly(modulus, field_element) == ZERO
    return {
        "source_word": word,
        "similitude_multiplier": multiplier,
        "compression_modulus_low_to_high": list(modulus),
        "primitive_root_coordinates": list(field_element),
        "primitive_root_is_root_of_compression_polynomial": root_verified,
        "primitive_root_multiplicative_order": order,
        "compression_matrix": [list(row) for row in matrix],
        **welded,
        "punctured_orbit_size": order,
        "punctured_stabilizer_size": 1 if order == 728 else 0,
    }


def build_receipt():
    beta_weld = weld(BETA_T, BETA)
    beta_substitution = poly_compose_at_one_minus_x(SELECTED_MODULUS)
    beta_order = multiplicative_order(BETA)

    inverter = primitive_receipt(
        INVERTER_SOURCE_WORD, 2, INVERTER_MODULUS, INVERTER_GAMMA, INVERTER_T
    )
    center = primitive_receipt(
        CENTER_SOURCE_WORD, 1, CENTER_MODULUS, CENTER_GAMMA, CENTER_T
    )

    presentation_paid = (
        beta_substitution == BETA_MODULUS
        and beta_weld["intertwining_verified"]
        and beta_weld["intertwiner_determinant_mod3"] != 0
    )
    multiplicative_paid = (
        center["primitive_root_is_root_of_compression_polynomial"]
        and center["primitive_root_multiplicative_order"] == 728
        and center["intertwining_verified"]
        and center["intertwiner_determinant_mod3"] != 0
        and center["cyclic_rank_e0"] == 6
        and center["breaks_swap01_at_e0"]
    )

    return {
        "schema": "dashi.j369.monster3b.selected_gf729_weld.v3",
        "source_producer": {
            "pr": 1098,
            "branch": "agent/e6-f3-exterior-square-maxcut-20261006",
            "receipt_path": "outputs/monster3b_atlas_compression_field_selector_20261012.json",
        },
        "selected_modulus_low_to_high": list(SELECTED_MODULUS),
        "earlier_beta_weld": {
            "source_word": "g2 g1 g2^-1 g1 g2^-1",
            "similitude_multiplier": 1,
            "compression_modulus_low_to_high": list(BETA_MODULUS),
            "affine_generator_change": "beta = 1 - alpha",
            "beta_coordinates": list(BETA),
            "polynomial_substitution_verified": beta_substitution == BETA_MODULUS,
            "multiplicative_order": beta_order,
            **beta_weld,
        },
        "primitive_inverter_comparator": inverter,
        "preferred_center_preserving_primitive_weld": center,
        "selected_field_presentation_weld_paid": presentation_paid,
        "selected_field_multiplicative_action_weld_paid": multiplicative_paid,
        "center_preserving_primitive_action_weld_paid": (
            multiplicative_paid and center["similitude_multiplier"] == 1
        ),
        "full_monster_semantic_action_recognition_paid": False,
        "boundary": (
            "A strict-symplectic source word is explicitly conjugate to multiplication "
            "by a primitive element of the already-selected GF(729), paying the full "
            "728-element punctured cyclic action while remaining eligible for one fixed "
            "central-character sector. The actual phase-resolved Monster state and "
            "Fin-90 multiplicity same-object action remain separate."
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
