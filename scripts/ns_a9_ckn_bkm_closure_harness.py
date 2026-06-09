#!/usr/bin/env python3
"""Small diagnostic for the A9 closure route.

This is a fail-closed local harness only. It consumes the same modeled A8
recursion and checks whether iterates decay below a tiny threshold, which is
the executable proxy for the A9 "iterate to zero then contradict singularity"
story.
"""

from __future__ import annotations

import argparse
import json

from ns_a8_full_local_defect_monotonicity_harness import iterate_case


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    steps = 40 if args.quick else 120
    cases = [
        iterate_case(0.5, 0.125, 1.0, 0.05, 0.5, 0.02, steps),
        iterate_case(0.5, 0.10, 1.0, 0.04, 0.5, 0.01, steps),
        iterate_case(0.6, 0.08, 0.9, 0.03, 0.5, 0.015, steps),
    ]
    tiny_threshold = 1.0e-3
    payload = {
        "contract": "A9 CKN/BKM closure diagnostic",
        "diagnostic_only": True,
        "promotion": {
            "a9_proved": False,
            "ns_clay_promoted": False,
            "terminal_promoted": False,
        },
        "summary": {
            "all_cases_decay_below_tiny_threshold": all(
                case.final_D < tiny_threshold for case in cases
            ),
            "tiny_threshold": tiny_threshold,
        },
        "cases": [
            {
                "theta": case.theta,
                "q": case.q,
                "final_D": case.final_D,
                "monotone_nonincreasing": case.monotone_nonincreasing,
            }
            for case in cases
        ],
    }

    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            "all_cases_decay_below_tiny_threshold="
            f"{payload['summary']['all_cases_decay_below_tiny_threshold']}"
        )
        print(f"tiny_threshold={tiny_threshold}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
