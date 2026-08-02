#!/usr/bin/env python3
"""Independent oracle for finite F3 subspaces and rational transport."""

from __future__ import annotations

from fractions import Fraction
from itertools import product

A = (
    (2, 0, 2, 1, 1, 2),
    (2, 1, 1, 2, 0, 2),
    (2, 2, 0, 2, 1, 1),
    (2, 2, 1, 1, 2, 0),
    (2, 1, 2, 0, 2, 1),
    (0, 1, 1, 1, 1, 1),
)

CANONICAL_PI50 = Fraction(
    16397605394050964443746106649,
    5219519906667074477262822481,
)

CANONICAL_ERROR_DENOMINATOR = (
    30975954210267369528087864730966858500331494237311153657
)


def encode(message: tuple[int, ...]) -> tuple[int, ...]:
    parity = tuple(
        sum(message[row] * A[row][column] for row in range(6)) % 3
        for column in range(6)
    )
    return message + parity


def dot(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    return sum(a * b for a, b in zip(left, right, strict=True)) % 3


def observer_map(value: Fraction) -> Fraction:
    return value / (value * value + 2)


def observer_cross_difference(x: Fraction, y: Fraction) -> Fraction:
    return x * (y * y + 2) - y * (x * x + 2)


def observer_factor_difference(x: Fraction, y: Fraction) -> Fraction:
    return (y - x) * (x * y - 2)


def main() -> None:
    messages = list(product(range(3), repeat=6))
    code = {encode(message) for message in messages}
    basis = tuple(
        encode(tuple(1 if coordinate == row else 0 for coordinate in range(6)))
        for row in range(6)
    )

    assert len(code) == 729
    assert all(dot(left, right) == 0 for left in code for right in basis)

    dual = {
        word
        for word in product(range(3), repeat=12)
        if all(dot(word, row) == 0 for row in basis)
    }
    assert len(dual) == 729
    assert dual == code

    sum_zero = {
        pair for pair in product(range(3), repeat=2)
        if (pair[0] + pair[1]) % 3 == 0
    }
    anti_diagonal = {(value, -value % 3) for value in range(3)}
    assert sum_zero == anti_diagonal == {(0, 0), (1, 2), (2, 1)}

    radius = Fraction(1, CANONICAL_ERROR_DENOMINATOR)
    lower = CANONICAL_PI50 - radius
    upper = CANONICAL_PI50 + radius
    assert lower < CANONICAL_PI50 < upper
    assert lower * upper > 2
    assert observer_map(upper) < observer_map(CANONICAL_PI50) < observer_map(lower)

    rational_samples = (
        (Fraction(3, 2), Fraction(2, 1)),
        (lower, CANONICAL_PI50),
        (CANONICAL_PI50, upper),
        (lower, upper),
    )
    assert all(
        observer_cross_difference(x, y)
        == observer_factor_difference(x, y)
        for x, y in rational_samples
    )

    print("Finite subspace/self-duality oracle passed.")
    print("  full F3^12 orthogonal complement equals the 729-word code")
    print("  ker(x+y) equals the anti-diagonal image in F3^2")
    print("  canonical pi interval transports antitonically to observer Y")


if __name__ == "__main__":
    main()
