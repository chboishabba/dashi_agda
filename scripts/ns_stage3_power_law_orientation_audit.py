#!/usr/bin/env python3
"""Exact audit for the three-condition output-relocation shell substitution."""
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


def evaluate(v: Orientation, left: Q, right: Q, output: Q) -> Q:
    return v.left * left + v.right * right + v.output * output


def verify_incidence() -> None:
    assert OUTPUT == Orientation(-1, -1, 1)
    assert FIRST == Orientation(1, -1, -1)
    assert SECOND == Orientation(-1, 1, -1)
    for vector in (OUTPUT, FIRST, SECOND):
        entries = (vector.left, vector.right, vector.output)
        assert entries.count(1) == 1
        assert entries.count(-1) == 2


def derive_scaled_row(orientation: Orientation) -> ScaledRow:
    # Physical exponent:
    #   -(2s-5/2)j - 2sd.
    # Auxiliary shell map for output-low relocation:
    #   j_L = j_R = J = j+d, j_O = j.
    return ScaledRow(
        constant_j=5,
        sobolev_j=-4,
        left_j=2 * orientation.left,
        right_j=2 * orientation.right,
        output_j=2 * orientation.output,
        sobolev_d=-4,
        left_d=2 * orientation.left,
        right_d=2 * orientation.right,
        output_d=0,
    )


def verify_literal_shell_substitution() -> None:
    assert derive_scaled_row(OUTPUT) == OUTPUT_ROW
    assert derive_scaled_row(FIRST) == FIRST_ROW
    assert derive_scaled_row(SECOND) == SECOND_ROW

    # Direct exact evaluation agrees with the normalized rows for sample rational
    # parameters. This is an algebra audit, not a positivity or convergence proof.
    samples = (
        (Q(8, 3), Q(1, 5), Q(2, 5), Q(3, 5), 4, 7),
        (Q(11, 4), Q(-1, 3), Q(1, 2), Q(2, 3), 2, 5),
    )
    for s, left, right, output, j, d in samples:
        physical = -(2 * s - Q(5, 2)) * j - 2 * s * d
        J = j + d
        for orientation, row in (
            (OUTPUT, OUTPUT_ROW),
            (FIRST, FIRST_ROW),
            (SECOND, SECOND_ROW),
        ):
            direct = physical + evaluate(orientation, left * J, right * J, output * j)
            scaled = Q(
                row.constant_j * j
                + row.sobolev_j * s * j
                + row.left_j * left * j
                + row.right_j * right * j
                + row.output_j * output * j
                + row.sobolev_d * s * d
                + row.left_d * left * d
                + row.right_d * right * d
                + row.output_d * output * d,
                2,
            )
            assert direct == scaled


def verify_candidate_boundary() -> None:
    status = {
        "grafakosTorresSignOrientation": True,
        "literalThreeConditionTemplate": True,
        "physicalWeightedExponent": True,
        "literalShellVariableSubstitution": True,
        "threeConditionAffineRows": True,
        "constructiveDyadicSeries": False,
        "affineWeightFamilySubstitution": False,
        "checkA": False,
    }
    assert status["grafakosTorresSignOrientation"]
    assert status["literalThreeConditionTemplate"]
    assert status["physicalWeightedExponent"]
    assert status["literalShellVariableSubstitution"]
    assert status["threeConditionAffineRows"]
    assert not status["constructiveDyadicSeries"]
    assert not status["affineWeightFamilySubstitution"]
    assert not status["checkA"]


def main() -> int:
    verify_incidence()
    verify_literal_shell_substitution()
    verify_candidate_boundary()
    print(
        "verified output-relocation Schur substitution: "
        "output/first/second sign incidence and exact j,J=j+d rows closed; "
        "constructive dyadic summation, affine-family substitution and Check A remain fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
