#!/usr/bin/env python3
"""Deterministic proxy for the Seiler-gap / continuum-route boundary.

This harness is a pure-stdlib diagnostic.  It does not prove Seiler 1982
compatibility, no spectral pollution, OS/Wightman reconstruction, a continuum
mass gap, or any Clay claim.  It assembles deterministic finite-volume gap
rows together with a no-spectral-pollution style barrier proxy and emits a
JSON receipt with promotion fixed false.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ym_seiler_continuum_route_harness.json")


@dataclass(frozen=True)
class GapCase:
    depth: int
    finite_gap_lower_bound: float
    truncation_error_budget: float
    holonomy_floor: float
    casimir_minimum: float
    c2_constant: float
    continuum_proxy_lower_bound: float
    monotone_vs_previous: bool
    positive_after_budget: bool


@dataclass(frozen=True)
class PollutionCase:
    name: str
    orthogonal_energy: float
    holonomy_energy: float
    sequence_mass_escape: float
    continuum_proxy_lower_bound: float
    near_vacuum_without_vacuum_convergence: bool
    spectral_pollution_detected: bool
    explanation: str


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="emit compact JSON to stdout")
    return parser.parse_args(argv)


def finite_gap_inputs() -> list[tuple[int, float, float, float]]:
    return [
        (2, 0.610, 0.180, 0.190),
        (3, 0.555, 0.105, 0.165),
        (4, 0.512, 0.072, 0.142),
        (5, 0.483, 0.051, 0.126),
        (6, 0.462, 0.039, 0.114),
    ]


def build_gap_cases() -> list[GapCase]:
    c2_constant = 0.8
    casimir_minimum = 0.25
    cases: list[GapCase] = []
    previous_proxy = -1.0
    for depth, finite_gap, error_budget, holonomy_floor in finite_gap_inputs():
        continuum_proxy = min(
            finite_gap - error_budget,
            c2_constant * casimir_minimum + 0.5 * holonomy_floor,
        )
        monotone_vs_previous = continuum_proxy <= previous_proxy or previous_proxy < 0.0
        cases.append(
            GapCase(
                depth=depth,
                finite_gap_lower_bound=finite_gap,
                truncation_error_budget=error_budget,
                holonomy_floor=holonomy_floor,
                casimir_minimum=casimir_minimum,
                c2_constant=c2_constant,
                continuum_proxy_lower_bound=continuum_proxy,
                monotone_vs_previous=monotone_vs_previous,
                positive_after_budget=continuum_proxy > 0.0,
            )
        )
        previous_proxy = continuum_proxy
    return cases


def build_pollution_cases(gap_cases: Sequence[GapCase]) -> list[PollutionCase]:
    continuum_floor = min(case.continuum_proxy_lower_bound for case in gap_cases)
    return [
        PollutionCase(
            name="vacuum_convergent_sequence",
            orthogonal_energy=0.0,
            holonomy_energy=0.0,
            sequence_mass_escape=0.0,
            continuum_proxy_lower_bound=continuum_floor,
            near_vacuum_without_vacuum_convergence=False,
            spectral_pollution_detected=False,
            explanation="The sequence is treated as converging to the vacuum, so it is not a pollution witness.",
        ),
        PollutionCase(
            name="holonomy_barrier_sequence",
            orthogonal_energy=0.231,
            holonomy_energy=0.118,
            sequence_mass_escape=0.014,
            continuum_proxy_lower_bound=continuum_floor,
            near_vacuum_without_vacuum_convergence=False,
            spectral_pollution_detected=False,
            explanation="A positive holonomy barrier and positive orthogonal energy keep the sequence above the proxy floor.",
        ),
        PollutionCase(
            name="would_be_pollution_sequence",
            orthogonal_energy=0.041,
            holonomy_energy=0.009,
            sequence_mass_escape=0.031,
            continuum_proxy_lower_bound=continuum_floor,
            near_vacuum_without_vacuum_convergence=True,
            spectral_pollution_detected=True,
            explanation="This synthetic row is flagged as a failure mode because the nonvacuum sequence falls below the proxy barrier.",
        ),
    ]


def build_summary() -> dict[str, object]:
    gap_cases = build_gap_cases()
    pollution_cases = build_pollution_cases(gap_cases)
    positive_cases = [case for case in gap_cases if case.positive_after_budget]
    detected_failures = [case for case in pollution_cases if case.spectral_pollution_detected]
    continuum_proxy_floor = min(case.continuum_proxy_lower_bound for case in gap_cases)

    summary = {
        "status": "fail_closed_boundary_proxy",
        "route": "finite gap lower bounds + spectral-pollution barrier proxy -> non-promoting continuum diagnostic",
        "gap_cases": [asdict(case) for case in gap_cases],
        "pollution_cases": [asdict(case) for case in pollution_cases],
        "metrics": {
            "case_count": len(gap_cases),
            "all_gap_rows_positive_after_budget": len(positive_cases) == len(gap_cases),
            "monotone_proxy_profile": all(case.monotone_vs_previous for case in gap_cases),
            "continuum_proxy_floor": continuum_proxy_floor,
            "spectral_pollution_failure_count": len(detected_failures),
            "no_spectral_pollution_proxy_passes": len(detected_failures) == 0,
        },
        "theorem_flags": {
            "seiler_1982_compatibility_proved_here": False,
            "no_spectral_pollution_proved_here": False,
            "os_wightman_reconstruction_proved_here": False,
            "continuum_mass_gap_promoted": False,
            "promotion": False,
        },
        "blockers": [
            "proxy rows are deterministic diagnostics only, not theorem carriers",
            "depth-limit no-spectral-pollution proof is absent",
            "flat 4D Euclidean continuum construction is absent",
            "OS/Wightman reconstruction is absent",
        ],
    }
    return summary


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    summary = build_summary()
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print(json.dumps({"json_output": str(args.json_output), "promotion": False}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
