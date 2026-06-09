#!/usr/bin/env python3
"""Finite proxy harness for the NS A1 Type-I/Lorentz-to-Abel mass route."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CaseResult:
    shell_decay: float
    type_i_constant: float
    window: int
    abel_rho: float
    shell_mass_total: float
    abel_average: float
    bounded_by_type_i_constant: bool


def build_case(shell_decay: float, type_i_constant: float, window: int, abel_rho: float) -> CaseResult:
    shell_masses = [type_i_constant * (shell_decay ** j) for j in range(window)]
    weights = [(abel_rho ** j) for j in range(window)]
    total_weight = sum(weights)
    weighted = sum(w * m for w, m in zip(weights, shell_masses))
    abel_average = weighted / total_weight
    return CaseResult(
        shell_decay=shell_decay,
        type_i_constant=type_i_constant,
        window=window,
        abel_rho=abel_rho,
        shell_mass_total=sum(shell_masses),
        abel_average=abel_average,
        bounded_by_type_i_constant=(abel_average <= type_i_constant + 1.0e-12),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    cases = [
        build_case(0.72, 1.8, 8, 0.82),
        build_case(0.68, 2.2, 10, 0.79),
        build_case(0.75, 1.5, 7, 0.85),
    ]
    payload = {
        "contract": "NS A1 Type-I/Lorentz to Abel mass route proxy",
        "diagnostic_only": True,
        "promotion": {
            "a1_proved": False,
            "ns_clay_promoted": False,
            "terminal_promoted": False,
        },
        "summary": {
            "all_cases_bounded_by_type_i_constant": all(
                case.bounded_by_type_i_constant for case in cases
            ),
            "max_abel_average": max(case.abel_average for case in cases),
        },
        "cases": [asdict(case) for case in cases],
    }

    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            "all_cases_bounded_by_type_i_constant="
            f"{payload['summary']['all_cases_bounded_by_type_i_constant']}"
        )
        print(f"max_abel_average={payload['summary']['max_abel_average']:.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

