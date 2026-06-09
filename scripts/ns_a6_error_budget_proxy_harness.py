#!/usr/bin/env python3
"""NS A6 synthetic error-budget proxy harness.

This pure-stdlib diagnostic combines seven A6 bookkeeping components:

  * diagonal residual
  * offdiag absorption
  * Abel LLN
  * localization cutoff
  * pressure commutator
  * pressure tail
  * Abel tail

It emits good profiles whose combined component errors decay below a tolerance,
and bad profiles where exactly one component has a persistent obstruction.  The
harness is synthetic bookkeeping only; it proves no Navier-Stokes theorem and
always emits promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ns_a6_error_budget_proxy_harness.json")

COMPONENTS = (
    "diagonal_residual",
    "offdiag_absorption",
    "abel_lln",
    "localization_cutoff",
    "pressure_commutator",
    "pressure_tail",
    "abel_tail",
)

GOOD_PROFILE_SPECS = (
    ("balanced_decay", 0.84, 0.0080),
    ("slow_tail_decay", 0.91, 0.0072),
    ("commutator_weighted_decay", 0.87, 0.0076),
)


@dataclass(frozen=True)
class DepthRow:
    profile: str
    kind: str
    depth: int
    component_errors: dict[str, float]
    total_error: float
    within_tolerance: bool


@dataclass(frozen=True)
class ComponentSummary:
    component: str
    max_good_error: float
    final_good_error: float
    min_bad_obstruction_error: float
    max_bad_non_obstruction_error: float
    bad_profiles_obstructed: int


@dataclass(frozen=True)
class ProfileSummary:
    name: str
    kind: str
    obstruction_component: str | None
    max_total_error: float
    min_total_error: float
    final_total_error: float
    rows_within_tolerance: int
    row_count: int
    expected_pass: bool
    observed_pass: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-depth", type=int, default=6)
    parser.add_argument("--max-depth", type=int, default=48)
    parser.add_argument("--tolerance", type=float, default=0.075)
    parser.add_argument("--bad-floor", type=float, default=0.115)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.min_depth < 1:
        raise ValueError("--min-depth must be positive")
    if args.max_depth < args.min_depth + 4:
        raise ValueError("--max-depth must be at least min-depth + 4")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if args.bad_floor <= args.tolerance:
        raise ValueError("--bad-floor must exceed --tolerance")


def component_weight(component: str) -> float:
    return 0.82 + 0.07 * (COMPONENTS.index(component) + 1)


def ripple(depth: int, component: str, phase: float) -> float:
    index = COMPONENTS.index(component) + 1
    return 1.0 + 0.045 * math.sin(0.37 * depth + phase * index)


def good_component_error(
    component: str, depth: int, min_depth: int, decay: float, scale: float, phase: float
) -> float:
    offset = depth - min_depth
    polynomial = (1.0 + offset) ** -1.22
    exponential = decay**offset
    return scale * component_weight(component) * exponential * polynomial * ripple(depth, component, phase)


def good_errors(
    depth: int, min_depth: int, decay: float, scale: float, phase: float
) -> dict[str, float]:
    return {
        component: good_component_error(component, depth, min_depth, decay, scale, phase)
        for component in COMPONENTS
    }


def bad_errors(
    component: str,
    depth: int,
    min_depth: int,
    decay: float,
    scale: float,
    bad_floor: float,
) -> dict[str, float]:
    errors = good_errors(depth, min_depth, decay, scale, phase=2.0)
    offset = depth - min_depth
    persistent = bad_floor * (1.0 + 0.035 * math.sin(0.23 * offset + COMPONENTS.index(component)))
    errors[component] = persistent + 0.012 / math.sqrt(1.0 + offset)
    return errors


def total_error(errors: dict[str, float]) -> float:
    return sum(abs(value) for value in errors.values())


def build_rows(args: argparse.Namespace) -> list[DepthRow]:
    rows: list[DepthRow] = []
    for profile_index, (name, decay, scale) in enumerate(GOOD_PROFILE_SPECS):
        phase = 0.5 + profile_index
        for depth in range(args.min_depth, args.max_depth + 1):
            errors = good_errors(depth, args.min_depth, decay, scale, phase)
            total = total_error(errors)
            rows.append(
                DepthRow(
                    profile=name,
                    kind="good_decaying",
                    depth=depth,
                    component_errors=errors,
                    total_error=total,
                    within_tolerance=total <= args.tolerance,
                )
            )
    for component in COMPONENTS:
        name = f"bad_{component}_obstruction"
        for depth in range(args.min_depth, args.max_depth + 1):
            errors = bad_errors(
                component=component,
                depth=depth,
                min_depth=args.min_depth,
                decay=0.88,
                scale=0.004,
                bad_floor=args.bad_floor,
            )
            total = total_error(errors)
            rows.append(
                DepthRow(
                    profile=name,
                    kind="bad_single_component_obstruction",
                    depth=depth,
                    component_errors=errors,
                    total_error=total,
                    within_tolerance=total <= args.tolerance,
                )
            )
    return rows


def profile_summaries(rows: Sequence[DepthRow], tolerance: float) -> list[ProfileSummary]:
    names = sorted({row.profile for row in rows})
    summaries: list[ProfileSummary] = []
    for name in names:
        profile_rows = [row for row in rows if row.profile == name]
        totals = [row.total_error for row in profile_rows]
        kind = profile_rows[0].kind
        obstruction = None
        if kind == "bad_single_component_obstruction":
            obstruction = name.removeprefix("bad_").removesuffix("_obstruction")
        expected_pass = kind == "good_decaying"
        observed_pass = all(row.within_tolerance for row in profile_rows)
        final_total = profile_rows[-1].total_error
        first_total = profile_rows[0].total_error
        summaries.append(
            ProfileSummary(
                name=name,
                kind=kind,
                obstruction_component=obstruction,
                max_total_error=max(totals),
                min_total_error=min(totals),
                final_total_error=final_total,
                rows_within_tolerance=sum(1 for row in profile_rows if row.within_tolerance),
                row_count=len(profile_rows),
                expected_pass=expected_pass,
                observed_pass=observed_pass,
                checks={
                    "expected_outcome_observed": observed_pass == expected_pass,
                    "final_error_below_initial_error": final_total < first_total,
                    "all_rows_within_tolerance": observed_pass,
                    "all_rows_above_tolerance": all(
                        row.total_error > tolerance for row in profile_rows
                    ),
                },
            )
        )
    return summaries


def component_summaries(rows: Sequence[DepthRow]) -> list[ComponentSummary]:
    good_rows = [row for row in rows if row.kind == "good_decaying"]
    bad_rows = [row for row in rows if row.kind == "bad_single_component_obstruction"]
    summaries: list[ComponentSummary] = []
    for component in COMPONENTS:
        good_values = [row.component_errors[component] for row in good_rows]
        final_good_values = [
            row.component_errors[component]
            for row in good_rows
            if row.depth == max(good_row.depth for good_row in good_rows)
        ]
        obstructed_rows = [
            row
            for row in bad_rows
            if row.profile == f"bad_{component}_obstruction"
        ]
        non_obstructed_values = [
            row.component_errors[component]
            for row in bad_rows
            if row.profile != f"bad_{component}_obstruction"
        ]
        summaries.append(
            ComponentSummary(
                component=component,
                max_good_error=max(good_values),
                final_good_error=max(final_good_values),
                min_bad_obstruction_error=min(
                    row.component_errors[component] for row in obstructed_rows
                ),
                max_bad_non_obstruction_error=max(non_obstructed_values),
                bad_profiles_obstructed=len({row.profile for row in obstructed_rows}),
            )
        )
    return summaries


def is_good_profile_decaying(rows: Sequence[DepthRow], profile: str) -> bool:
    profile_rows = [row for row in rows if row.profile == profile]
    midpoint = len(profile_rows) // 2
    first_half_max = max(row.total_error for row in profile_rows[:midpoint])
    second_half_max = max(row.total_error for row in profile_rows[midpoint:])
    return second_half_max < first_half_max and profile_rows[-1].total_error < profile_rows[0].total_error


def build_summary(args: argparse.Namespace) -> dict[str, object]:
    validate_args(args)
    rows = build_rows(args)
    profiles = profile_summaries(rows, args.tolerance)
    components = component_summaries(rows)

    good_rows = [row for row in rows if row.kind == "good_decaying"]
    bad_rows = [row for row in rows if row.kind == "bad_single_component_obstruction"]
    max_good_total_error = max(row.total_error for row in good_rows)
    min_bad_total_error = min(row.total_error for row in bad_rows)

    good_profile_names = [name for name, _decay, _scale in GOOD_PROFILE_SPECS]
    validation_flags = {
        "all_good_rows_within_tolerance": all(row.total_error <= args.tolerance for row in good_rows),
        "all_good_profiles_decay": all(is_good_profile_decaying(rows, name) for name in good_profile_names),
        "all_bad_rows_exceed_tolerance": all(row.total_error > args.tolerance for row in bad_rows),
        "each_bad_profile_has_one_named_obstruction": all(
            profile.obstruction_component in COMPONENTS
            for profile in profiles
            if profile.kind == "bad_single_component_obstruction"
        ),
        "each_component_has_bad_obstruction_profile": all(
            summary.bad_profiles_obstructed == 1 for summary in components
        ),
        "bad_obstruction_exceeds_good_component_max": all(
            summary.min_bad_obstruction_error > summary.max_good_error
            for summary in components
        ),
        "promotion_is_false": True,
    }
    ok = all(validation_flags.values()) and max_good_total_error <= args.tolerance
    ok = ok and min_bad_total_error > args.tolerance

    return {
        "control": {
            "O": "Lane 4 Kolmogorov NS A6 synthetic error-budget proxy harness.",
            "R": "Combine seven component errors into good decaying profiles and bad single-component obstruction profiles.",
            "C": "scripts/ns_a6_error_budget_proxy_harness.py",
            "S": "Pure synthetic finite bookkeeping; no manifest, docs, or Agda surface is modified.",
            "L": "component profiles -> total error budget -> good/bad separation -> fail-closed JSON validation",
            "P": "Use deterministic decays for admissible profiles and persistent floors for one-component obstructions.",
            "G": "promotion=false always; this diagnostic cannot promote a Navier-Stokes result.",
            "F": "Does not prove diagonal/offdiag/Abel/localization/pressure estimates for the PDE.",
        },
        "ok": ok,
        "promotion": False,
        "component_names": list(COMPONENTS),
        "tolerance": args.tolerance,
        "bad_floor": args.bad_floor,
        "parameters": {
            "min_depth": args.min_depth,
            "max_depth": args.max_depth,
            "depth_count": args.max_depth - args.min_depth + 1,
        },
        "max_good_total_error": max_good_total_error,
        "min_bad_total_error": min_bad_total_error,
        "validation_flags": validation_flags,
        "component_summaries": [asdict(summary) for summary in components],
        "profile_summaries": [asdict(summary) for summary in profiles],
        "rows": [asdict(row) for row in rows],
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    summary = build_summary(args)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("NS A6 error-budget proxy harness")
        print(f"ok={str(summary['ok']).lower()}")
        print("promotion=false")
        print(f"max_good_total_error={summary['max_good_total_error']:.6g}")
        print(f"min_bad_total_error={summary['min_bad_total_error']:.6g}")
        print(f"tolerance={summary['tolerance']:.6g}")
    return 0 if summary["ok"] and not summary["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
