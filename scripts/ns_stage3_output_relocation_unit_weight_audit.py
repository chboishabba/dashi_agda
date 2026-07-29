#!/usr/bin/env python3
"""Exact unit-weight Check A audit for output relocation."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path


def text(value: F) -> str:
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


def unit_rows(s: F) -> dict[str, F]:
    low = F(5) - F(4) * s
    gap = -F(4) * s
    return {
        "outputLow": low,
        "outputGap": gap,
        "firstLow": low,
        "firstGap": gap,
        "secondLow": low,
        "secondGap": gap,
    }


def verify() -> dict[str, object]:
    probes: dict[str, object] = {}
    for name, s in (
        ("lowerEndpoint", F(5, 2)),
        ("representativeInterior", F(8, 3)),
        ("upperEndpoint", F(3)),
    ):
        rows = unit_rows(s)
        assert all(value < 0 for value in rows.values())
        probes[name] = {
            "s": text(s),
            "rows": {key: text(value) for key, value in rows.items()},
        }

    # Symbolically, for s > 5/2:
    # 5 - 4s < 5 - 10 = -5 and -4s < -10.
    lower = F(5, 2)
    assert F(5) - F(4) * lower == F(-5)
    assert -F(4) * lower == F(-10)

    return {
        "unitAffineData": {
            "base": ["0", "0", "0"],
            "direction": ["0", "0", "0"],
            "epsilon": "1/4",
        },
        "symbolicRows": {
            "allLow": "5-4s",
            "allGap": "-4s",
            "targetInterval": "5/2<s<3",
        },
        "probes": probes,
        "decision": {
            "unitWeightsAllowedBySchurCarrier": True,
            "unitWeightPositivityFinitenessConjugatePowers": True,
            "sixRowsStrict": True,
            "commonPositiveEpsilonInterval": "all epsilon>0",
            "symbolicCheckA": True,
            "constructiveDyadicTail": False,
            "analyticArchetype": False,
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
        "verified unit-weight output-relocation Check A: B=D=0, all low rows "
        "equal 5-4s and all gap rows equal -4s, hence all six are strict on "
        "5/2<s<3; constructive dyadic summation remains open"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
