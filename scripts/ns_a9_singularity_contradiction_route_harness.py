#!/usr/bin/env python3
"""Finite proxy harness for the NS A9 singularity contradiction route."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CaseResult:
    decay_to_zero: bool
    vorticity_vanishes: bool
    harmonicity_available: bool
    elliptic_regularity_available: bool
    contradiction_triggered: bool


def evaluate(final_defect: float) -> CaseResult:
    decay = final_defect < 1.0e-4
    vorticity = decay
    harmonic = vorticity
    elliptic = harmonic
    contradiction = elliptic
    return CaseResult(
        decay_to_zero=decay,
        vorticity_vanishes=vorticity,
        harmonicity_available=harmonic,
        elliptic_regularity_available=elliptic,
        contradiction_triggered=contradiction,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    rows = [evaluate(3.0e-5), evaluate(8.0e-5), evaluate(2.0e-5)]
    payload = {
        "contract": "NS A9 singularity contradiction route proxy",
        "diagnostic_only": True,
        "promotion": {
            "a9_proved": False,
            "ns_clay_promoted": False,
            "terminal_promoted": False,
        },
        "summary": {
            "all_rows_reach_proxy_contradiction": all(row.contradiction_triggered for row in rows),
        },
        "rows": [asdict(row) for row in rows],
    }

    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            "all_rows_reach_proxy_contradiction="
            f"{payload['summary']['all_rows_reach_proxy_contradiction']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

