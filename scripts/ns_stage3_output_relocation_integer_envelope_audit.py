#!/usr/bin/env python3
"""Exact integer-envelope audit for output-relocation dyadic sums."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path


def geometric_partial(ratio: F, cutoff: int) -> F:
    return sum((ratio ** n for n in range(cutoff + 1)), F(0))


def verify() -> dict[str, object]:
    low_ratio = F(1, 4)
    gap_ratio = F(1, 32)
    low_sum = F(4, 3)
    gap_sum = F(32, 31)
    product = F(128, 93)

    assert (F(1) - low_ratio) * low_sum == 1
    assert (F(1) - gap_ratio) * gap_sum == 1
    assert low_sum * gap_sum == product

    for cutoff in range(0, 128):
        assert geometric_partial(low_ratio, cutoff) <= low_sum
        assert geometric_partial(gap_ratio, cutoff) <= gap_sum

    probes = {}
    for name, s in (
        ("lowerEndpoint", F(5, 2)),
        ("representativeInterior", F(8, 3)),
        ("upperEndpoint", F(3)),
    ):
        low_decay = F(2) * s - F(5, 2)
        gap_decay = F(2) * s
        assert low_decay >= F(5, 2) > F(2)
        assert gap_decay >= F(5)
        probes[name] = {
            "s": str(s),
            "lowDecay": str(low_decay),
            "gapDecay": str(gap_decay),
        }

    return {
        "integerEnvelopes": {
            "lowExponent": 2,
            "gapExponent": 5,
            "lowRatio": "1/4",
            "gapRatio": "1/32",
        },
        "cutoffUniformBounds": {
            "low": "4/3",
            "gap": "32/31",
            "product": "128/93",
        },
        "probes": probes,
        "decision": {
            "arbitraryRealRatioGeometricTheoremRequired": False,
            "rationalGeometricConstantsClosed": True,
            "constructiveBaseTwoExponentAntitonicityBridge": False,
            "cutoffUniformSeriesClosed": False,
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
        "verified output-relocation integer geometric envelope: low decay >2 "
        "and gap decay >=5 on the target range, giving ratios 1/4 and 1/32, "
        "sums 4/3 and 32/31, and product bound 128/93; only constructive "
        "base-two exponent antitonicity remains"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
