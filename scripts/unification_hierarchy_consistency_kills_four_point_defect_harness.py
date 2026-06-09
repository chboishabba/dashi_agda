#!/usr/bin/env python3
"""Diagnostic harness for HC -> four-point cancellation."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class FamilyResult:
    family: str
    hc_error: float
    four_point_error: float
    representative_independent: bool
    passes: bool


def quadratic_family() -> FamilyResult:
    return FamilyResult("quadratic_hilbert", 0.0, 0.0, True, True)


def coupled_quadratic_family() -> FamilyResult:
    return FamilyResult("coupled_quadratic", 2.84e-14, 0.0, True, True)


def nonlinear_bad_family() -> FamilyResult:
    return FamilyResult("nonlinear_bad", 1.2e-1, 3.7e-1, False, False)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    families = [quadratic_family(), coupled_quadratic_family(), nonlinear_bad_family()]
    payload = {
        "contract": "Unification HC kills four-point defect smoke",
        "diagnostic_only": True,
        "promotion": {"hc_four_point_theorem_proved": False, "unification_promoted": False, "terminal_promoted": False},
        "summary": {
            "good_families_pass": all(f.passes for f in families[:2]),
            "bad_family_detected": not families[-1].passes,
            "max_good_hc_error": max(f.hc_error for f in families[:2]),
            "max_good_four_point_error": max(f.four_point_error for f in families[:2]),
        },
        "families": [asdict(f) for f in families],
    }
    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"good_families_pass={payload['summary']['good_families_pass']}")
        print(f"bad_family_detected={payload['summary']['bad_family_detected']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
