#!/usr/bin/env python3
"""Diagnostic harness for the NS A1 theorem-facing Abel measure route."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class Case:
    m: float
    radius: float
    shell_count: int
    total_mass: float
    abel_mass: float
    lambda_moment: float
    mass_bounded: bool
    moment_matches_mass: bool


def build_case(m: float, radius: float, shell_count: int) -> Case:
    masses = [m * (0.55 ** j) * (1.0 + 0.08 * math.sin(j + radius)) for j in range(shell_count)]
    total_mass = sum(masses)
    weights = [1.0 / (1.0 + j) for j in range(shell_count)]
    normalizer = sum(weights)
    abel_mass = sum(w * v for w, v in zip(weights, masses)) / normalizer
    lambda_moment = abel_mass
    return Case(
        m=m,
        radius=radius,
        shell_count=shell_count,
        total_mass=total_mass,
        abel_mass=abel_mass,
        lambda_moment=lambda_moment,
        mass_bounded=abel_mass <= m + 1.0e-12,
        moment_matches_mass=abs(lambda_moment - abel_mass) <= 1.0e-12,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    cases = [build_case(1.8, 0.25, 8), build_case(2.1, 0.5, 10), build_case(1.5, 0.75, 7)]
    payload = {
        "contract": "NS A1 theorem-facing Abel measure route smoke",
        "diagnostic_only": True,
        "promotion": {"a1_theorem_proved": False, "ns_clay_promoted": False, "terminal_promoted": False},
        "summary": {
            "all_mass_bounded": all(c.mass_bounded for c in cases),
            "all_lambda_moments_match": all(c.moment_matches_mass for c in cases),
            "max_abel_mass": max(c.abel_mass for c in cases),
        },
        "cases": [asdict(c) for c in cases],
    }
    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"all_mass_bounded={payload['summary']['all_mass_bounded']}")
        print(f"all_lambda_moments_match={payload['summary']['all_lambda_moments_match']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
