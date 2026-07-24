#!/usr/bin/env python3
"""Generate exact rational LDL certificates for mean-zero path Poincare bounds.

For P_L use the coordinates

    f = (y_0, ..., y_{L-2}, -sum_i y_i)

and certify

    (1/L^2) ||f||_2^2 <= E_P_L(f).

JSON output records the exact matrices.  With --agda-output the same certificate
is emitted as an Agda module that reconstructs the quadratic identity with the
rational ring solver and feeds it to BalabanRationalLDLCertificate.
"""

from __future__ import annotations

import argparse
import json
import re
from fractions import Fraction
from pathlib import Path
from typing import Iterable

Matrix = list[list[Fraction]]


def zeros(rows: int, columns: int) -> Matrix:
    return [[Fraction(0) for _ in range(columns)] for _ in range(rows)]


def transpose(matrix: Matrix) -> Matrix:
    return [list(row) for row in zip(*matrix)]


def matmul(left: Matrix, right: Matrix) -> Matrix:
    if not left or not right:
        return []
    if len(left[0]) != len(right):
        raise ValueError("matrix dimensions do not match")
    columns = transpose(right)
    return [
        [sum((a * b for a, b in zip(row, column)), Fraction(0))
         for column in columns]
        for row in left
    ]


def matsub(left: Matrix, right: Matrix) -> Matrix:
    return [
        [a - b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def scale(scalar: Fraction, matrix: Matrix) -> Matrix:
    return [[scalar * entry for entry in row] for row in matrix]


def identity(size: int) -> Matrix:
    result = zeros(size, size)
    for index in range(size):
        result[index][index] = Fraction(1)
    return result


def mean_zero_basis(length: int) -> Matrix:
    result = zeros(length, length - 1)
    for column in range(length - 1):
        result[column][column] = Fraction(1)
        result[length - 1][column] = Fraction(-1)
    return result


def path_laplacian(length: int) -> Matrix:
    result = zeros(length, length)
    for index in range(length - 1):
        result[index][index] += 1
        result[index + 1][index + 1] += 1
        result[index][index + 1] -= 1
        result[index + 1][index] -= 1
    return result


def ldl(matrix: Matrix) -> tuple[Matrix, list[Fraction]]:
    size = len(matrix)
    lower = identity(size)
    diagonal = [Fraction(0) for _ in range(size)]
    for column in range(size):
        correction = sum(
            (lower[column][k] ** 2 * diagonal[k] for k in range(column)),
            Fraction(0),
        )
        diagonal[column] = matrix[column][column] - correction
        if diagonal[column] <= 0:
            raise ValueError(
                f"non-positive LDL pivot at {column}: {diagonal[column]}"
            )
        for row in range(column + 1, size):
            correction = sum(
                (lower[row][k] * lower[column][k] * diagonal[k]
                 for k in range(column)),
                Fraction(0),
            )
            lower[row][column] = (
                matrix[row][column] - correction
            ) / diagonal[column]
    return lower, diagonal


def diagonal_matrix(values: Iterable[Fraction]) -> Matrix:
    diagonal = list(values)
    result = zeros(len(diagonal), len(diagonal))
    for index, value in enumerate(diagonal):
        result[index][index] = value
    return result


def certificate_data(
    length: int,
) -> tuple[Matrix, Matrix, Matrix, Matrix, Matrix, list[Fraction]]:
    if length < 2:
        raise ValueError("path length must be at least two")
    basis = mean_zero_basis(length)
    basis_transpose = transpose(basis)
    gram = matmul(basis_transpose, basis)
    energy = matmul(matmul(basis_transpose, path_laplacian(length)), basis)
    constrained = matsub(
        energy,
        scale(Fraction(1, length * length), gram),
    )
    lower, diagonal = ldl(constrained)
    reconstructed = matmul(
        matmul(lower, diagonal_matrix(diagonal)),
        transpose(lower),
    )
    if reconstructed != constrained:
        raise AssertionError("LDL reconstruction failed")
    return basis, gram, energy, constrained, lower, diagonal


def encode_fraction(value: Fraction) -> dict[str, int | str]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "text": str(value),
    }


def encode_matrix(matrix: Matrix) -> list[list[dict[str, int | str]]]:
    return [[encode_fraction(entry) for entry in row] for row in matrix]


def generate(length: int) -> dict[str, object]:
    basis, gram, energy, constrained, lower, diagonal = certificate_data(length)
    return {
        "path_length": length,
        "poincare_constant": encode_fraction(Fraction(1, length * length)),
        "mean_zero_basis": encode_matrix(basis),
        "gram_matrix": encode_matrix(gram),
        "energy_matrix": encode_matrix(energy),
        "constrained_matrix": encode_matrix(constrained),
        "lower_unit_triangular": encode_matrix(lower),
        "positive_diagonal": [encode_fraction(value) for value in diagonal],
        "verified_exactly": True,
        "agda_emitter_available": True,
        "agda_consumed": False,
    }


def agda_fraction(value: Fraction) -> str:
    if value == 0:
        return "0ℚ"
    positive = f"(+ {abs(value.numerator)} / {value.denominator})"
    return positive if value > 0 else f"(- {positive})"


def right_sum(terms: list[str]) -> str:
    if not terms:
        return "0ℚ"
    result = terms[-1]
    for term in reversed(terms[:-1]):
        result = f"({term} + {result})"
    return result


def linear_form(coefficients: list[Fraction], variables: list[str]) -> str:
    return right_sum([
        f"{agda_fraction(coefficient)} * {variable}"
        for coefficient, variable in zip(coefficients, variables)
        if coefficient != 0
    ])


def generate_agda_module(length: int, module_name: str) -> str:
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_.]*", module_name):
        raise ValueError(f"invalid Agda module name: {module_name!r}")

    _, _, _, _, lower, diagonal = certificate_data(length)
    variables = [f"y{index}" for index in range(length - 1)]
    fields = " ".join(variables)
    constructor = f"pathCoordinates {fields}"
    final_coordinate = f"(- {right_sum(variables)})"
    coordinates = variables + [final_coordinate]

    norm_expression = right_sum([f"sq ({value})" for value in coordinates])
    energy_expression = right_sum([
        f"sqDiff ({coordinates[index + 1]}) ({coordinates[index]})"
        for index in range(length - 1)
    ])

    forms = [
        linear_form(
            [lower[row][column] for row in range(length - 1)],
            variables,
        )
        for column in range(length - 1)
    ]
    form_definitions = "\n\n".join(
        f"form{index} : PathCoordinates → ℚ\n"
        f"form{index} ({constructor}) = {form}"
        for index, form in enumerate(forms)
    )
    term_lines = [
        f"  ldlTerm {agda_fraction(pivot)} form{index} "
        f"(nonnegativeFraction {pivot.numerator} {pivot.denominator})"
        for index, pivot in enumerate(diagonal)
    ]
    terms = "\n  ∷ ".join(term_lines) + "\n  ∷ []"
    arguments = " ".join(variables)
    constant = Fraction(1, length * length)

    return f'''module {module_name} where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate

record PathCoordinates : Set where
  constructor pathCoordinates
  field
    {fields} : ℚ

open PathCoordinates public

pathNormSq : PathCoordinates → ℚ
pathNormSq ({constructor}) = {norm_expression}

pathEnergy : PathCoordinates → ℚ
pathEnergy ({constructor}) = {energy_expression}

coercivityConstant : ℚ
coercivityConstant = {agda_fraction(constant)}

{form_definitions}

nonnegativeFraction :
  ∀ (numerator denominator : ℕ) {{_ : ℕ.NonZero denominator}} →
  0ℚ ≤ (+ numerator / denominator)
nonnegativeFraction numerator denominator =
  let
    instance
      fractionNonnegative : NonNegative (+ numerator / denominator)
      fractionNonnegative = ℚP.normalize-nonNeg numerator denominator
  in
  ℚP.nonNegative⁻¹ (+ numerator / denominator)

pathTerms : List (LDLTerm PathCoordinates)
pathTerms =
{terms}

pathLDLDecompositionRaw : ∀ {arguments} →
  pathEnergy ({constructor})
  ≡ coercivityConstant * pathNormSq ({constructor})
    + sumTermValues pathTerms ({constructor})
pathLDLDecompositionRaw = ℚRing.solve-∀

pathLDLDecomposition : ∀ coordinate →
  pathEnergy coordinate
  ≡ coercivityConstant * pathNormSq coordinate
    + sumTermValues pathTerms coordinate
pathLDLDecomposition ({constructor}) =
  pathLDLDecompositionRaw {arguments}

pathLDLCertificate : RationalLDLCertificate PathCoordinates
pathLDLCertificate = record
  {{ normSq = pathNormSq
  ; energy = pathEnergy
  ; coercivityConstant = coercivityConstant
  ; terms = pathTerms
  ; decomposition = pathLDLDecomposition
  }}

pathPoincare : ∀ coordinate →
  coercivityConstant * pathNormSq coordinate ≤ pathEnergy coordinate
pathPoincare = ldlCertificatePoincare pathLDLCertificate

generatedPathLDLReconstructionLevel : ProofLevel
generatedPathLDLReconstructionLevel = computed

generatedPathLDLConsumptionLevel : ProofLevel
generatedPathLDLConsumptionLevel = machineChecked
'''


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("length", type=int)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--agda-output", type=Path)
    parser.add_argument(
        "--agda-module",
        default="DASHI.Physics.YangMills.GeneratedPathLDLCertificate",
    )
    return parser.parse_args()


def main() -> None:
    arguments = parse_args()
    result = generate(arguments.length)
    encoded = json.dumps(result, indent=2, sort_keys=True)
    if arguments.output:
        arguments.output.write_text(encoded + "\n", encoding="utf-8")
    if arguments.agda_output:
        arguments.agda_output.write_text(
            generate_agda_module(arguments.length, arguments.agda_module),
            encoding="utf-8",
        )
    print(encoded)


if __name__ == "__main__":
    main()
