#!/usr/bin/env python3
"""NS pressure-localization sub-budget proxy harness.

This pure-stdlib diagnostic aggregates synthetic pressure-localization
components for the A6 Navier-Stokes pointwise-to-Abel transfer lane:

  * cutoff/Riesz commutator
  * local Calderon-Zygmund core
  * harmonic tail
  * pressure tail
  * annular cutoff
  * epsilon-gradient absorption
  * Abel recenter/lower-order residual

Good profiles have separated or decaying component budgets below tolerance.
Bad profiles contain one persistent blocking component.  This is finite
bookkeeping only; it proves no pressure estimate or Clay theorem and always
emits promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ns_pressure_localization_subbudget_proxy_harness.json")
EPS = 1.0e-12

COMPONENTS = (
    "cutoff_riesz_commutator",
    "local_calderon_zygmund_core",
    "harmonic_tail",
    "pressure_tail",
    "annular_cutoff",
    "epsilon_gradient_absorption",
    "abel_recenter_lower_order",
)


@dataclass(frozen=True)
class ProfileSpec:
    name: str
    family: str
    description: str
    expected_good: bool
    decay: float
    scale: float
    separation_gain: float
    smoothness_gain: float
    abel_gain: float
    blocker: str | None = None


@dataclass(frozen=True)
class BudgetRow:
    profile: str
    family: str
    level: int
    dyadic_scale: float
    annular_separation: float
    component_errors: dict[str, float]
    combined_error: float
    tolerance: float
    blocking_component: str | None
    within_tolerance: bool


@dataclass(frozen=True)
class ProfileSummary:
    name: str
    family: str
    description: str
    expected_good: bool
    observed_pass: bool
    classification: str
    blocking_component: str | None
    row_count: int
    initial_combined_error: float
    final_combined_error: float
    decay_ratio: float
    min_combined_error: float
    max_combined_error: float
    rows_within_tolerance: int
    final_component_errors: dict[str, float]
    checks: dict[str, bool]


@dataclass(frozen=True)
class ComponentSummary:
    component: str
    max_good_error: float
    final_good_error: float
    min_bad_blocker_error: float
    max_bad_non_blocker_error: float
    bad_profiles_blocked: int


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", type=int, default=12, help="Number of refinement levels.")
    parser.add_argument("--tolerance", type=float, default=1.0e-2)
    parser.add_argument("--bad-floor", type=float, default=3.0e-2)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.levels < 6:
        raise ValueError("--levels must be at least 6")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if args.bad_floor <= args.tolerance:
        raise ValueError("--bad-floor must exceed --tolerance")


def profile_specs() -> list[ProfileSpec]:
    return [
        ProfileSpec(
            name="good_smooth_separated_budget",
            family="smooth_separated",
            description="Smooth cutoff, separated annulus, and recentered Abel residual.",
            expected_good=True,
            decay=0.70,
            scale=0.0060,
            separation_gain=1.28,
            smoothness_gain=1.35,
            abel_gain=1.18,
        ),
        ProfileSpec(
            name="good_harmonic_tail_absorbed_budget",
            family="harmonic_tail_absorbed",
            description="Mean-subtracted harmonic tail with stronger exterior decay.",
            expected_good=True,
            decay=0.66,
            scale=0.0064,
            separation_gain=1.45,
            smoothness_gain=1.12,
            abel_gain=1.20,
        ),
        ProfileSpec(
            name="good_epsilon_gradient_absorbed_budget",
            family="epsilon_gradient_absorbed",
            description="Gradient leakage is routed into epsilon absorption and lower-order decay.",
            expected_good=True,
            decay=0.68,
            scale=0.0059,
            separation_gain=1.20,
            smoothness_gain=1.30,
            abel_gain=1.35,
        ),
        *[
            ProfileSpec(
                name=f"bad_{component}_blocker",
                family="single_component_blocker",
                description=f"Persistent {component.replace('_', ' ')} obstruction blocks the sub-budget.",
                expected_good=False,
                decay=0.72,
                scale=0.0036,
                separation_gain=1.15,
                smoothness_gain=1.08,
                abel_gain=1.10,
                blocker=component,
            )
            for component in COMPONENTS
        ],
    ]


def component_weight(component: str) -> float:
    return 0.82 + 0.08 * (COMPONENTS.index(component) + 1)


def component_gain(component: str, spec: ProfileSpec) -> float:
    if component == "cutoff_riesz_commutator":
        return spec.smoothness_gain
    if component == "local_calderon_zygmund_core":
        return 1.10 * spec.smoothness_gain
    if component == "harmonic_tail":
        return spec.separation_gain
    if component == "pressure_tail":
        return 0.95 * spec.separation_gain
    if component == "annular_cutoff":
        return math.sqrt(spec.separation_gain * spec.smoothness_gain)
    if component == "epsilon_gradient_absorption":
        return 1.16 * spec.abel_gain
    if component == "abel_recenter_lower_order":
        return spec.abel_gain
    raise KeyError(component)


def ripple(component: str, level: int, phase: float) -> float:
    index = COMPONENTS.index(component) + 1
    return 1.0 + 0.035 * math.sin(0.61 * level + phase * index)


def good_component_error(component: str, spec: ProfileSpec, level: int) -> float:
    dyadic_scale = 2.0 ** (-(level + 1))
    polynomial = (level + 1.0) ** -1.08
    decaying = spec.decay**level
    base = spec.scale * component_weight(component) * polynomial * decaying
    gain = component_gain(component, spec)
    moment_gain = dyadic_scale ** (0.18 if component != "local_calderon_zygmund_core" else 0.06)
    return base * ripple(component, level, spec.scale * 1000.0) * moment_gain / gain


def component_errors(spec: ProfileSpec, level: int, bad_floor: float) -> dict[str, float]:
    errors = {component: good_component_error(component, spec, level) for component in COMPONENTS}
    if spec.blocker is not None:
        blocker_index = COMPONENTS.index(spec.blocker) + 1
        persistent = bad_floor * (1.0 + 0.04 * math.sin(0.43 * level + blocker_index))
        errors[spec.blocker] = persistent + 0.0045 / math.sqrt(level + 1.0)
    return errors


def combined_error(errors: dict[str, float]) -> float:
    # Pressure localization budgets are routed by the largest remaining
    # unabsorbed component; a single blocker should keep the profile failing.
    return max(abs(value) for value in errors.values())


def build_rows(args: argparse.Namespace) -> list[BudgetRow]:
    rows: list[BudgetRow] = []
    for spec in profile_specs():
        for level in range(args.levels):
            errors = component_errors(spec, level, args.bad_floor)
            combined = combined_error(errors)
            blocker = max(errors, key=errors.get)
            rows.append(
                BudgetRow(
                    profile=spec.name,
                    family=spec.family,
                    level=level,
                    dyadic_scale=2.0 ** (-(level + 1)),
                    annular_separation=1.0 + spec.separation_gain * math.sqrt(level + 1.0),
                    component_errors=errors,
                    combined_error=combined,
                    tolerance=args.tolerance,
                    blocking_component=blocker if combined > args.tolerance else None,
                    within_tolerance=combined <= args.tolerance,
                )
            )
    return rows


def summarize_profiles(rows: Sequence[BudgetRow]) -> list[ProfileSummary]:
    specs_by_name = {spec.name: spec for spec in profile_specs()}
    summaries: list[ProfileSummary] = []
    for name in sorted(specs_by_name):
        spec = specs_by_name[name]
        profile_rows = [row for row in rows if row.profile == name]
        if not profile_rows:
            raise ValueError(f"profile {name} produced no rows")
        initial = profile_rows[0].combined_error
        final = profile_rows[-1].combined_error
        observed_pass = all(row.within_tolerance for row in profile_rows)
        max_error = max(row.combined_error for row in profile_rows)
        min_error = min(row.combined_error for row in profile_rows)
        final_components = profile_rows[-1].component_errors
        expected_outcome_observed = observed_pass == spec.expected_good
        summaries.append(
            ProfileSummary(
                name=name,
                family=spec.family,
                description=spec.description,
                expected_good=spec.expected_good,
                observed_pass=observed_pass,
                classification="pass" if observed_pass else "fail",
                blocking_component=spec.blocker,
                row_count=len(profile_rows),
                initial_combined_error=initial,
                final_combined_error=final,
                decay_ratio=final / max(initial, EPS),
                min_combined_error=min_error,
                max_combined_error=max_error,
                rows_within_tolerance=sum(1 for row in profile_rows if row.within_tolerance),
                final_component_errors=final_components,
                checks={
                    "expected_outcome_observed": expected_outcome_observed,
                    "good_final_below_tolerance": (final <= profile_rows[-1].tolerance)
                    if spec.expected_good
                    else True,
                    "bad_blocker_above_tolerance": (final > profile_rows[-1].tolerance)
                    if not spec.expected_good
                    else True,
                    "final_error_not_increasing_for_good": (final < initial)
                    if spec.expected_good
                    else True,
                    "declared_blocker_is_final_max": (
                        spec.blocker is None
                        or max(final_components, key=final_components.get) == spec.blocker
                    ),
                },
            )
        )
    return summaries


def summarize_components(rows: Sequence[BudgetRow]) -> list[ComponentSummary]:
    good_rows = [row for row in rows if row.family != "single_component_blocker"]
    bad_rows = [row for row in rows if row.family == "single_component_blocker"]
    summaries: list[ComponentSummary] = []
    for component in COMPONENTS:
        good_values = [row.component_errors[component] for row in good_rows]
        final_level = max(row.level for row in good_rows)
        final_good_values = [
            row.component_errors[component] for row in good_rows if row.level == final_level
        ]
        blocker_profile = f"bad_{component}_blocker"
        blocker_values = [
            row.component_errors[component] for row in bad_rows if row.profile == blocker_profile
        ]
        non_blocker_values = [
            row.component_errors[component] for row in bad_rows if row.profile != blocker_profile
        ]
        summaries.append(
            ComponentSummary(
                component=component,
                max_good_error=max(good_values),
                final_good_error=max(final_good_values),
                min_bad_blocker_error=min(blocker_values),
                max_bad_non_blocker_error=max(non_blocker_values),
                bad_profiles_blocked=sum(
                    1
                    for row in bad_rows
                    if row.profile == blocker_profile and row.component_errors[component] > row.tolerance
                ),
            )
        )
    return summaries


def row_summaries(rows: Sequence[BudgetRow]) -> list[dict[str, object]]:
    return [
        {
            "profile": row.profile,
            "family": row.family,
            "level": row.level,
            "combined_error": row.combined_error,
            "blocking_component": row.blocking_component,
            "within_tolerance": row.within_tolerance,
            "component_errors": row.component_errors,
        }
        for row in rows
    ]


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    validate_args(args)
    rows = build_rows(args)
    profile_summaries = summarize_profiles(rows)
    component_summaries = summarize_components(rows)
    good_cases = [asdict(summary) for summary in profile_summaries if summary.expected_good]
    bad_cases = [asdict(summary) for summary in profile_summaries if not summary.expected_good]

    all_expected = all(
        summary.checks["expected_outcome_observed"] for summary in profile_summaries
    )
    good_all_pass = all(summary.observed_pass for summary in profile_summaries if summary.expected_good)
    bad_all_fail = all(
        not summary.observed_pass for summary in profile_summaries if not summary.expected_good
    )
    blocker_declared = all(
        summary.checks["declared_blocker_is_final_max"]
        for summary in profile_summaries
        if not summary.expected_good
    )
    finite_nonnegative = all(
        math.isfinite(row.combined_error)
        and row.combined_error >= 0.0
        and all(math.isfinite(value) and value >= 0.0 for value in row.component_errors.values())
        for row in rows
    )
    component_separation = all(
        summary.min_bad_blocker_error > args.bad_floor
        and summary.max_good_error < args.tolerance
        for summary in component_summaries
    )

    validation_flags = {
        "good_profiles_pass": good_all_pass,
        "bad_profiles_fail": bad_all_fail,
        "expected_outcomes_observed": all_expected,
        "blocker_components_dominate_bad_profiles": blocker_declared,
        "component_separation_observed": component_separation,
        "finite_nonnegative_errors": finite_nonnegative,
        "diagnostic_only": True,
        "promotion": False,
    }
    ok = all(
        bool(value)
        for key, value in validation_flags.items()
        if key not in {"diagnostic_only", "promotion"}
    )

    aggregate_metrics = {
        "profile_count": len(profile_summaries),
        "good_profile_count": len(good_cases),
        "bad_profile_count": len(bad_cases),
        "component_count": len(COMPONENTS),
        "row_count": len(rows),
        "max_good_combined_error": max(
            summary.max_combined_error for summary in profile_summaries if summary.expected_good
        ),
        "max_bad_final_combined_error": max(
            summary.final_combined_error for summary in profile_summaries if not summary.expected_good
        ),
        "min_bad_final_combined_error": min(
            summary.final_combined_error for summary in profile_summaries if not summary.expected_good
        ),
        "worst_good_decay_ratio": max(
            summary.decay_ratio for summary in profile_summaries if summary.expected_good
        ),
    }

    return {
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": {
            "levels": args.levels,
            "tolerance": args.tolerance,
            "bad_floor": args.bad_floor,
            "components": list(COMPONENTS),
        },
        "good_cases": good_cases,
        "bad_cases": bad_cases,
        "aggregate_metrics": aggregate_metrics,
        "component_summaries": [asdict(summary) for summary in component_summaries],
        "validation_flags": validation_flags,
        "row_summaries": row_summaries(rows),
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = build_payload(args)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
