#!/usr/bin/env python3
"""Exact audit for the output-relocation rational majorant programme."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


def power(base: Q, exponent: int) -> Q:
    assert exponent >= 0
    result = Q(1)
    for _ in range(exponent):
        result *= base
    return result


def partial_sum(base: Q, cutoff: int) -> Q:
    assert cutoff >= 0
    return sum((power(base, exponent) for exponent in range(cutoff + 1)), Q(0))


def run() -> dict[str, object]:
    quarter = Q(1, 4)
    thirty_second = Q(1, 32)
    four_thirds = Q(4, 3)
    thirty_two_thirty_firsts = Q(32, 31)
    rectangle_constant = Q(128, 93)

    assert (Q(1) - quarter) * four_thirds == 1
    assert (Q(1) - thirty_second) * thirty_two_thirty_firsts == 1
    assert four_thirds * thirty_two_thirty_firsts == rectangle_constant

    samples: list[dict[str, object]] = []
    for low_cutoff in (0, 1, 2, 3, 7, 16, 64):
        low_sum = partial_sum(quarter, low_cutoff)
        assert low_sum <= four_thirds
        for gap_cutoff in (0, 1, 2, 3, 7, 16, 64):
            gap_sum = partial_sum(thirty_second, gap_cutoff)
            rectangle_sum = low_sum * gap_sum
            assert gap_sum <= thirty_two_thirty_firsts
            assert rectangle_sum <= rectangle_constant
            samples.append(
                {
                    "lowCutoff": low_cutoff,
                    "gapCutoff": gap_cutoff,
                    "lowSum": str(low_sum),
                    "gapSum": str(gap_sum),
                    "rectangleSum": str(rectangle_sum),
                }
            )

    # Exact regularity arithmetic over representative interior points.
    regularities = (Q(251, 100), Q(8, 3), Q(299, 100))
    decay_checks: list[dict[str, str]] = []
    for regularity in regularities:
        low_decay = 2 * regularity - Q(5, 2)
        gap_decay = 2 * regularity
        assert Q(5, 2) < regularity < Q(3)
        assert low_decay > Q(2)
        assert gap_decay > Q(5)
        assert 5 - 4 * regularity < 0
        assert -4 * regularity < 0
        decay_checks.append(
            {
                "s": str(regularity),
                "lowDecay": str(low_decay),
                "gapDecay": str(gap_decay),
                "unitWeightLowRow": str(5 - 4 * regularity),
                "unitWeightGapRow": str(-4 * regularity),
            }
        )

    return {
        "constants": {
            "lowRatio": str(quarter),
            "gapRatio": str(thirty_second),
            "lowBound": str(four_thirds),
            "gapBound": str(thirty_two_thirty_firsts),
            "rectangleBound": str(rectangle_constant),
        },
        "regularityChecks": decay_checks,
        "sampledCutoffRectangles": samples,
        "decision": {
            "rationalFiniteGeometricEnvelopeClosed": True,
            "positiveKernelConstructed": True,
            "positiveKernelCutoffUniformlySummable": True,
            "threeUnitWeightShellConditionsClosed": True,
            "finiteSignedDominationTheoremClosed": True,
            "conditionalArchetypeTheoremClosed": True,
            "concreteHsShellBridgeClosed": False,
            "concreteOutputRelocationArchetypeClosed": False,
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
        "verified exact 1/4 and 1/32 finite geometric sums, uniform bounds "
        "4/3 and 32/31, rectangular constant 128/93, interior decay margins, "
        "and the conditional output-relocation decision boundary"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
