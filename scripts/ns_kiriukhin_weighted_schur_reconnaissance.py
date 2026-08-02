#!/usr/bin/env python3
"""Exact finite weighted-Schur reconnaissance for sparse orbit transfer matrices."""

from __future__ import annotations

from collections import defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import permutations, product

Complex = tuple[Fraction, Fraction]
Vector = list[Complex]
Mode = tuple[int, int, int]
Orbit = Mode


def c(real: int | Fraction = 0, imag: int | Fraction = 0) -> Complex:
    return Fraction(real), Fraction(imag)


def add(a: Complex, b: Complex) -> Complex:
    return a[0] + b[0], a[1] + b[1]


def multiply(a: Complex, b: Complex) -> Complex:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(real: Fraction, value: Complex) -> Complex:
    return real * value[0], real * value[1]


def conjugate(value: Complex) -> Complex:
    return value[0], -value[1]


def minus_i(value: Complex) -> Complex:
    return value[1], -value[0]


def vector_scale(scalar: Complex, value: Vector) -> Vector:
    return [multiply(scalar, entry) for entry in value]


def mode_dot(mode: Mode, value: Vector) -> Complex:
    total = c()
    for coordinate, entry in zip(mode, value, strict=True):
        total = add(total, scale(Fraction(coordinate), entry))
    return total


def hermitian(left: Vector, right: Vector) -> Complex:
    total = c()
    for a, b in zip(left, right, strict=True):
        total = add(total, multiply(conjugate(a), b))
    return total


def norm_squared(mode: Mode) -> int:
    return sum(coordinate * coordinate for coordinate in mode)


def leray(mode: Mode, value: Vector) -> Vector:
    radial = mode_dot(mode, value)
    denominator = Fraction(norm_squared(mode))
    return [
        add(entry, scale(Fraction(-coordinate, 1) / denominator, radial))
        for coordinate, entry in zip(mode, value, strict=True)
    ]


def ordered_nonlinearity(
    state: dict[Mode, Vector], output: Mode, left: Mode, right: Mode
) -> Vector:
    raw = vector_scale(mode_dot(right, state[left]), state[right])
    return [minus_i(entry) for entry in leray(output, raw)]


def negate_mode(mode: Mode) -> Mode:
    return tuple(-coordinate for coordinate in mode)  # type: ignore[return-value]


def reality_complete(positive: dict[Mode, Vector]) -> dict[Mode, Vector]:
    state = dict(positive)
    for mode, value in positive.items():
        state[negate_mode(mode)] = [conjugate(entry) for entry in value]
    return state


def witness_state() -> dict[Mode, Vector]:
    return reality_complete(
        {
            (-1, 0, 3): [c(3, 3), c(-3, -3), c(1, 1)],
            (2, -3, -3): [c(-3), c(), c(-2)],
            (1, -3, 0): [c(3, -3), c(1, -1), c()],
        }
    )


def optimized_support_state() -> dict[Mode, Vector]:
    return reality_complete(
        {
            (3, 5, -1): [c(23, -8), c(-12, 10), c(9, 26)],
            (5, 4, -4): [c(-4, 16), c(22, -2), c(17, 18)],
            (8, 9, -5): [c(1, 8), c(3, -1), c(7, 11)],
        }
    )


SIGNED_PERMUTATIONS = tuple(
    product(permutations(range(3)), product((-1, 1), repeat=3))
)


def transform_mode(
    mode: Mode, transform: tuple[tuple[int, ...], tuple[int, ...]]
) -> Mode:
    permutation, signs = transform
    return tuple(
        signs[index] * mode[permutation[index]] for index in range(3)
    )  # type: ignore[return-value]


def orbit(mode: Mode) -> set[Mode]:
    return {transform_mode(mode, transform) for transform in SIGNED_PERMUTATIONS}


def canonical_orbit(mode: Mode) -> Orbit:
    return min(orbit(mode))


def raw_orbit_transfer_matrix(
    state: dict[Mode, Vector],
) -> tuple[list[Orbit], dict[tuple[Orbit, Orbit], Fraction]]:
    support = set(state)
    matrix: dict[tuple[Orbit, Orbit], Fraction] = defaultdict(Fraction)

    for output in state:
        output_orbit = canonical_orbit(output)
        output_orbit_size = len(orbit(output))
        for left in state:
            right = tuple(output[index] - left[index] for index in range(3))
            if right not in support:
                continue
            source_orbit = canonical_orbit(left)
            contribution = Fraction(norm_squared(output), output_orbit_size) * hermitian(
                state[output], ordered_nonlinearity(state, output, left, right)
            )[0]
            matrix[(output_orbit, source_orbit)] += contribution

    indices = sorted({row for row, _ in matrix} | {column for _, column in matrix})
    return indices, dict(matrix)


def integer_power(base: int, exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(base**exponent)
    return Fraction(1, base ** (-exponent))


def weighted_constants(
    indices: list[Orbit],
    matrix: dict[tuple[Orbit, Orbit], Fraction],
    row_exponent: int,
    column_exponent: int,
) -> tuple[Fraction, Fraction, Fraction]:
    row_weight = {
        index: integer_power(1 + norm_squared(index), row_exponent)
        for index in indices
    }
    column_weight = {
        index: integer_power(1 + norm_squared(index), column_exponent)
        for index in indices
    }

    row_constant = max(
        sum(
            abs(matrix.get((row, column), Fraction())) * column_weight[column]
            for column in indices
        )
        / row_weight[row]
        for row in indices
    )
    column_constant = max(
        sum(
            row_weight[row] * abs(matrix.get((row, column), Fraction()))
            for row in indices
        )
        / column_weight[column]
        for column in indices
    )
    return row_constant, column_constant, row_constant * column_constant


def best_one_weight(
    indices: list[Orbit], matrix: dict[tuple[Orbit, Orbit], Fraction]
) -> tuple[Fraction, int, Fraction, Fraction]:
    candidates = []
    for exponent in range(-8, 9):
        row, column, product_value = weighted_constants(
            indices, matrix, exponent, exponent
        )
        candidates.append((product_value, exponent, row, column))
    return min(candidates)


def best_two_weight(
    indices: list[Orbit], matrix: dict[tuple[Orbit, Orbit], Fraction]
) -> tuple[Fraction, int, int, Fraction, Fraction]:
    candidates = []
    for row_exponent in range(-6, 7):
        for column_exponent in range(-6, 7):
            row, column, product_value = weighted_constants(
                indices, matrix, row_exponent, column_exponent
            )
            candidates.append(
                (product_value, row_exponent, column_exponent, row, column)
            )
    return min(candidates)


def decimal_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def kiriukhin_profile(index: Orbit) -> Decimal:
    # s = 8/3 lies strictly inside the official 5/2 < s < 3 overlap.
    radius = Decimal(norm_squared(index)).sqrt()
    exponent = Decimal(8) / Decimal(3)
    return ((Decimal(2) - exponent) * radius.ln()).exp() + (
        (Decimal(6) - Decimal(3) * exponent) * radius.ln()
    ).exp()


def decimal_weighted_product(
    indices: list[Orbit],
    matrix: dict[tuple[Orbit, Orbit], Fraction],
    row_weight,
    column_weight,
) -> Decimal:
    row_constant = max(
        sum(
            decimal_fraction(abs(matrix.get((row, column), Fraction())))
            * column_weight(column)
            for column in indices
        )
        / row_weight(row)
        for row in indices
    )
    column_constant = max(
        sum(
            row_weight(row)
            * decimal_fraction(abs(matrix.get((row, column), Fraction())))
            for row in indices
        )
        / column_weight(column)
        for column in indices
    )
    return row_constant * column_constant


def verify_state(label: str, state: dict[Mode, Vector]) -> dict[str, object]:
    for mode, value in state.items():
        assert mode_dot(mode, value) == c()
        assert state[negate_mode(mode)] == [conjugate(entry) for entry in value]

    indices, matrix = raw_orbit_transfer_matrix(state)
    unweighted = weighted_constants(indices, matrix, 0, 0)
    one_weight = best_one_weight(indices, matrix)
    two_weight = best_two_weight(indices, matrix)

    same_profile_product = decimal_weighted_product(
        indices, matrix, kiriukhin_profile, kiriukhin_profile
    )
    inverse_to_profile_product = decimal_weighted_product(
        indices,
        matrix,
        lambda index: Decimal(1) / kiriukhin_profile(index),
        kiriukhin_profile,
    )

    return {
        "label": label,
        "orbit_count": len(indices),
        "indices": indices,
        "matrix": matrix,
        "unweighted": unweighted,
        "best_one_weight": one_weight,
        "best_two_weight": two_weight,
        "kiriukhin_same_profile_product": same_profile_product,
        "kiriukhin_inverse_to_profile_product": inverse_to_profile_product,
    }


def main() -> int:
    getcontext().prec = 80
    witness = verify_state("witness", witness_state())
    optimized = verify_state("optimized", optimized_support_state())

    assert witness["orbit_count"] == 2
    assert optimized["orbit_count"] == 3

    assert witness["unweighted"] == (
        Fraction(517),
        Fraction(752),
        Fraction(388_784),
    )
    assert witness["best_one_weight"] == (
        Fraction(7_484_092, 23),
        1,
        Fraction(5_687, 23),
        Fraction(1_316),
    )

    assert optimized["unweighted"] == (
        Fraction(2_336_395, 6),
        Fraction(3_751_853, 6),
        Fraction(8_765_810_589_935, 36),
    )
    assert optimized["best_one_weight"] == (
        Fraction(8_765_810_589_935, 36),
        0,
        Fraction(2_336_395, 6),
        Fraction(3_751_853, 6),
    )
    assert optimized["best_two_weight"] == (
        Fraction(500_941_503_391_525, 2_088),
        0,
        -1,
        Fraction(133_518_425, 12_528),
        Fraction(22_511_118),
    )

    witness_unweighted_product = decimal_fraction(witness["unweighted"][2])
    optimized_unweighted_product = decimal_fraction(optimized["unweighted"][2])
    assert witness["kiriukhin_same_profile_product"] > witness_unweighted_product
    assert optimized["kiriukhin_same_profile_product"] > optimized_unweighted_product
    assert optimized["kiriukhin_inverse_to_profile_product"] < optimized_unweighted_product

    print(
        "verified finite weighted-Schur reconnaissance: witness raw matrix has "
        "2 orbit indices and a gamma=1 one-weight product improvement; optimized "
        "support has 3 orbit indices, no improving one-weight integer power in "
        "[-8,8], and a small exact two-function improvement at exponents (0,-1); "
        "the Kiriukhin s=8/3 profile is not a self-dual improvement on both states"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
