#!/usr/bin/env python3
"""Exact Grafakos--Torres three-weight and Kiriukhin rank audit."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path


def rank(matrix: list[list[F]]) -> int:
    work = [row[:] for row in matrix]
    rows = len(work)
    cols = len(work[0]) if rows else 0
    pivot_row = 0
    for column in range(cols):
        pivot = next((r for r in range(pivot_row, rows) if work[r][column]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        scale = work[pivot_row][column]
        work[pivot_row] = [entry / scale for entry in work[pivot_row]]
        for r in range(rows):
            if r == pivot_row:
                continue
            factor = work[r][column]
            if factor:
                work[r] = [
                    entry - factor * pivot_entry
                    for entry, pivot_entry in zip(
                        work[r], work[pivot_row], strict=True
                    )
                ]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def text(value: F) -> str:
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


def run() -> dict[str, object]:
    # Grafakos--Torres Section 5 diagonal example:
    # p=q=r'=3, alpha_1=alpha_2=alpha, n=3.
    dimension = F(3)
    alpha = F(1)
    epsilon = F(1, 4)
    cancellation_order = F(3)

    left_exponent = F(2) * alpha + dimension / F(3) - F(2, 3) * epsilon
    right_exponent = left_exponent
    output_exponent = F(2) * alpha + dimension / F(6) - F(2, 3) * epsilon

    assert left_exponent == F(17, 6)
    assert right_exponent == F(17, 6)
    assert output_exponent == F(7, 3)

    # The stated general cancellation inequalities specialize to
    # L > 3 alpha - epsilon > epsilon > 0.
    lower_cancellation_target = F(3) * alpha - epsilon
    margins = {
        "epsilonPositive": epsilon,
        "targetAboveEpsilon": lower_cancellation_target - epsilon,
        "cancellationOrderAboveTarget": cancellation_order
        - lower_cancellation_target,
    }
    assert all(value > 0 for value in margins.values())
    assert margins == {
        "epsilonPositive": F(1, 4),
        "targetAboveEpsilon": F(5, 2),
        "cancellationOrderAboveTarget": F(1, 4),
    }

    source_threshold = 10
    first_strict_far_gap = 11
    assert first_strict_far_gap > source_threshold

    # Kiriukhin Theorem 6.5 at the repository's representative s=8/3.
    s = F(8, 3)
    slow_row_power = F(2) - s
    fast_row_power = F(6) - F(3) * s
    assert slow_row_power == F(-2, 3)
    assert fast_row_power == F(-2)

    # The raw theorem supplies output-row decay but no homogeneity equations
    # for either partial adjoint.  Each row-profile branch therefore has one
    # independent equation for three weight exponents.
    row_only_matrix = [[F(0), F(0), F(1)]]
    row_rank = rank(row_only_matrix)
    unknown_count = 3
    nullity = unknown_count - row_rank
    assert row_rank == 1
    assert nullity == 2

    # Adding two genuinely independent partial-adjoint equations would make
    # the exponent system determinate.  This template checks the required
    # rank transition without claiming that these are the NS coefficients.
    full_rank_template = [
        [F(0), F(0), F(1)],
        [F(1), F(0), F(-1)],
        [F(0), F(1), F(-1)],
    ]
    assert rank(full_rank_template) == 3

    return {
        "grafakosTorresDiagonal": {
            "dimension": text(dimension),
            "alpha": text(alpha),
            "epsilon": text(epsilon),
            "leftExponent": text(left_exponent),
            "rightExponent": text(right_exponent),
            "outputExponent": text(output_exponent),
            "cancellationOrder": text(cancellation_order),
            "strictMargins": {key: text(value) for key, value in margins.items()},
            "sourceWaveletThreshold": source_threshold,
            "firstStrictFarGap": first_strict_far_gap,
        },
        "kiriukhinAtEightThirds": {
            "s": text(s),
            "slowRowPower": text(slow_row_power),
            "fastRowPower": text(fast_row_power),
            "rowOnlyRank": row_rank,
            "threeWeightUnknowns": unknown_count,
            "rowOnlyNullity": nullity,
            "fullThreeEquationTemplateRank": 3,
        },
        "decision": {
            "threeFunctionFrameworkPrimary": True,
            "twoFunctionRouteIsFrozenOutputSpecialization": True,
            "rowTheoremAloneDeterminesThreeWeights": False,
            "partialAdjointHomogeneityLedgersRequired": True,
            "sourceThresholdPortableWithoutAdapter": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    result = run()
    if args.json:
        args.json.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(
        "verified Grafakos--Torres diagonal weights "
        "(17/6, 17/6, 7/3), strict epsilon/cancellation margins, "
        "source gap threshold 10, and Kiriukhin row-only exponent "
        "rank 1 with nullity 2"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
