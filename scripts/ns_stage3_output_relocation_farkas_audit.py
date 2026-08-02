#!/usr/bin/env python3
"""Exact primal/dual classification of the output-relocation affine ansatz."""
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
    return pivot_row


def determinant3(matrix: list[list[F]]) -> F:
    a, b, c = matrix[0]
    d, e, f = matrix[1]
    g, h, i = matrix[2]
    return (
        a * (e * i - f * h)
        - b * (d * i - f * g)
        + c * (d * h - e * g)
    )


def matvec(matrix: list[list[F]], vector: list[F]) -> list[F]:
    return [
        sum(
            (entry * value for entry, value in zip(row, vector, strict=True)),
            F(0),
        )
        for row in matrix
    ]


def text(value: F) -> str:
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


BASE_MATRIX = [
    [F(-2), F(-2), F(2)],
    [F(2), F(-2), F(-2)],
    [F(-2), F(2), F(-2)],
]
DIRECTION_MATRIX = [[-entry for entry in row] for row in BASE_MATRIX]
DUAL_MULTIPLIERS_SCALED = [F(2), F(1), F(1)]
OUTPUT_GAP_WEIGHT_ROW = [F(-2), F(-2), F(0)]


def base_solution(s: F) -> list[F]:
    value = (F(5) - F(4) * s) / F(2)
    return [value, value, value]


def rows_at(s: F, base: list[F]) -> dict[str, F]:
    left, right, output = base
    return {
        "outputLow": F(5) - F(4) * s - F(2) * left - F(2) * right
        + F(2) * output,
        "outputGap": -F(4) * s - F(2) * left - F(2) * right,
        "firstLow": F(5) - F(4) * s + F(2) * left - F(2) * right
        - F(2) * output,
        "firstGap": -F(4) * s + F(2) * left - F(2) * right,
        "secondLow": F(5) - F(4) * s - F(2) * left + F(2) * right
        - F(2) * output,
        "secondGap": -F(4) * s - F(2) * left + F(2) * right,
    }


def verify() -> dict[str, object]:
    assert determinant3(BASE_MATRIX) == F(-32)
    assert rank(BASE_MATRIX) == 3
    assert determinant3(DIRECTION_MATRIX) == F(32)
    assert rank(DIRECTION_MATRIX) == 3

    # Exact integral dual combination:
    # 2*r0 + r1 + r2 = 2*(-2,-2,0).
    combination = [
        sum(
            DUAL_MULTIPLIERS_SCALED[r] * BASE_MATRIX[r][c]
            for r in range(3)
        )
        for c in range(3)
    ]
    assert combination == [F(2) * entry for entry in OUTPUT_GAP_WEIGHT_ROW]

    probes: dict[str, dict[str, object]] = {}
    for name, s in (
        ("lowerEndpoint", F(5, 2)),
        ("representativeInterior", F(8, 3)),
        ("upperEndpoint", F(3)),
    ):
        rhs = [F(4) * s - F(5)] * 3
        base = base_solution(s)
        assert matvec(BASE_MATRIX, base) == rhs
        values = rows_at(s, base)
        assert values["outputLow"] == 0
        assert values["firstLow"] == 0
        assert values["secondLow"] == 0
        assert values["outputGap"] == F(4) * s - F(10)
        assert values["firstGap"] == -F(4) * s
        assert values["secondGap"] == -F(4) * s

        outcome = "zero-slack" if values["outputGap"] == 0 else "infeasible"
        if s > F(5, 2):
            assert values["outputGap"] > 0
            assert outcome == "infeasible"
        probes[name] = {
            "s": text(s),
            "base": [text(value) for value in base],
            "rows": {key: text(value) for key, value in values.items()},
            "outcome": outcome,
        }

    # Any direction preserving all three low-shell equalities solves M D = 0.
    # Since det(M)=32, the only such direction is zero; all slopes vanish.
    zero_direction = [F(0), F(0), F(0)]
    assert matvec(DIRECTION_MATRIX, zero_direction) == zero_direction

    return {
        "baseSystem": {
            "determinant": "-32",
            "rank": 3,
            "solution": "B_L=B_R=B_O=(5-4s)/2",
        },
        "dualCertificate": {
            "scaledMultipliers": ["2", "1", "1"],
            "commonScale": "2",
            "combinedRow": [text(value) for value in combination],
            "forcedOutputGap": "4s-10",
        },
        "directionSystem": {
            "determinant": "32",
            "rank": 3,
            "onlyPreservingDirection": ["0", "0", "0"],
        },
        "probes": probes,
        "decision": {
            "baseSystemClassified": True,
            "directionSystemClassified": True,
            "commonIntervalComputed": True,
            "commonPositiveIntervalNonempty": False,
            "symbolicCheckA": False,
            "currentHomogeneityPreservingAffineAnsatzInfeasible": True,
            "allPossibleThreeWeightAnsatzesInfeasible": False,
            "proceedToDyadicAdapterForCurrentAnsatz": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    result = verify()
    if args.json:
        args.json.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(
        "verified output-relocation affine classification: base det=-32 and "
        "unique B=(5-4s)/2; preserving-direction det=32 and D=0; exact dual "
        "witness forces output gap 4s-10, so the endpoint is zero-slack and "
        "every 5/2<s<3 point is infeasible for this ansatz"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
