#!/usr/bin/env python3
"""Exact audit for output-relocation shell and affine-family substitution."""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q


@dataclass(frozen=True)
class Orientation:
    left: int
    right: int
    output: int


@dataclass(frozen=True)
class ScaledRow:
    constant_j: int
    sobolev_j: int
    left_j: int
    right_j: int
    output_j: int
    sobolev_d: int
    left_d: int
    right_d: int
    output_d: int


OUTPUT = Orientation(-1, -1, 1)
FIRST = Orientation(1, -1, -1)
SECOND = Orientation(-1, 1, -1)

OUTPUT_ROW = ScaledRow(5, -4, -2, -2, 2, -4, -2, -2, 0)
FIRST_ROW = ScaledRow(5, -4, 2, -2, -2, -4, 2, -2, 0)
SECOND_ROW = ScaledRow(5, -4, -2, 2, -2, -4, -2, 2, 0)


def derive_scaled_row(o: Orientation) -> ScaledRow:
    return ScaledRow(5, -4, 2 * o.left, 2 * o.right, 2 * o.output,
                     -4, 2 * o.left, 2 * o.right, 0)


def epsilon_slope(coefficients: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(-c for c in coefficients)


def verify_all() -> None:
    assert derive_scaled_row(OUTPUT) == OUTPUT_ROW
    assert derive_scaled_row(FIRST) == FIRST_ROW
    assert derive_scaled_row(SECOND) == SECOND_ROW

    expected = {
        "output": ((2, 2, -2), (2, 2, 0)),
        "first": ((-2, 2, 2), (-2, 2, 0)),
        "second": ((2, -2, 2), (2, -2, 0)),
    }
    for name, row in (("output", OUTPUT_ROW), ("first", FIRST_ROW), ("second", SECOND_ROW)):
        low = epsilon_slope((row.left_j, row.right_j, row.output_j))
        gap = epsilon_slope((row.left_d, row.right_d, row.output_d))
        assert (low, gap) == expected[name]

    samples = ((Q(8, 3), Q(1, 5), Q(2, 5), Q(3, 5), 4, 7),)
    for s, left, right, output, j, d in samples:
        physical = -(2 * s - Q(5, 2)) * j - 2 * s * d
        J = j + d
        for o, row in ((OUTPUT, OUTPUT_ROW), (FIRST, FIRST_ROW), (SECOND, SECOND_ROW)):
            direct = physical + o.left * left * J + o.right * right * J + o.output * output * j
            scaled = Q(row.constant_j * j + row.sobolev_j * s * j
                       + row.left_j * left * j + row.right_j * right * j + row.output_j * output * j
                       + row.sobolev_d * s * d + row.left_d * left * d
                       + row.right_d * right * d + row.output_d * output * d, 2)
            assert direct == scaled

    status = {
        "literalShellVariableSubstitution": True,
        "threeConditionAffineRows": True,
        "sixEpsilonSlopes": True,
        "constructiveDyadicSeries": False,
        "numericBasesDirections": False,
        "positiveCommonEpsilon": False,
        "checkA": False,
    }
    assert all(status[k] for k in ("literalShellVariableSubstitution", "threeConditionAffineRows", "sixEpsilonSlopes"))
    assert not any(status[k] for k in ("constructiveDyadicSeries", "numericBasesDirections", "positiveCommonEpsilon", "checkA"))


def main() -> int:
    verify_all()
    print(
        "verified output-relocation literal rows and six affine epsilon slopes; "
        "constructive dyadic summation, numeric bases/directions, positive epsilon and Check A remain fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
