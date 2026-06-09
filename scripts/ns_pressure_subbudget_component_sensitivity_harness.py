#!/usr/bin/env python3
"""Sensitivity sweep for the NS pressure-localization sub-budget proxy.

This pure-stdlib diagnostic stress-tests the seven synthetic components used
by ``ns_pressure_localization_subbudget_proxy_harness.py``:

  * cutoff/Riesz commutator
  * local Calderon-Zygmund core
  * harmonic tail
  * pressure tail
  * annular cutoff
  * epsilon-gradient absorption
  * Abel recenter/lower-order residual

The sweep varies tolerance, bad floor, annular separation, smoothness gain,
and epsilon absorption.  Good regimes should remain below tolerance through
stable ranges; bad single-component blockers should remain visible.  This is
diagnostic bookkeeping only.  It proves no pressure estimate, no A6 theorem,
and no Clay claim; the emitted payload always has promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ns_pressure_subbudget_component_sensitivity.json")
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
class SweepRegime:
    name: str
    sweep: int
    tolerance: float
    bad_floor: float
    annular_separation: float
    smoothness_gain: float
    epsilon_absorption: float
    stable_range: bool


@dataclass(frozen=True)
class ProfileSpec:
    name: str
    family: str
    description: str
    expected_good: bool
    base_scale: float
    decay: float
    separation_gain: float
    smoothness_gain: float
    abel_gain: float
    epsilon_gain: float
    blocker: str | None = None


@dataclass(frozen=True)
class SensitivityRow:
    regime: str
    sweep: int
    profile: str
    family: str
    level: int
    tolerance: float
    bad_floor: float
    annular_separation: float
    smoothness_gain: float
    epsilon_absorption: float
    component_errors: dict[str, float]
    combined_error: float
    blocking_component: str | None
    within_tolerance: bool


@dataclass(frozen=True)
class CaseSummary:
    profile: str
    family: str
    expected_good: bool
    observed_pass: bool
    stable_regime_pass: bool
    classification: str
    blocker: str | None
    row_count: int
    regime_count: int
    max_combined_error: float
    max_stable_combined_error: float
    min_bad_blocker_error: float | None
    final_stable_combined_error: float
    worst_regime: str
    final_component_errors: dict[str, float]
    checks: dict[str, bool]


@dataclass(frozen=True)
class ComponentSensitivity:
    component: str
    max_good_stable_error: float
    min_bad_blocker_stable_error: float
    max_bad_non_blocker_stable_error: float
    sensitivity_span: float
    visible_blocker_regimes: int
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", type=int, default=10)
    parser.add_argument("--sweeps", type=int, default=9)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.levels < 6:
        raise ValueError("--levels must be at least 6")
    if args.sweeps < 5:
        raise ValueError("--sweeps must be at least 5")


def profile_specs() -> list[ProfileSpec]:
    return [
        ProfileSpec(
            name="good_smooth_separated",
            family="good",
            description="Smooth cutoff with separated annulus and recentered Abel residual.",
            expected_good=True,
            base_scale=0.0047,
            decay=0.68,
            separation_gain=1.34,
            smoothness_gain=1.42,
            abel_gain=1.18,
            epsilon_gain=1.10,
        ),
        ProfileSpec(
            name="good_tail_absorbed",
            family="good",
            description="Mean-subtracted harmonic and pressure tails with annular decay.",
            expected_good=True,
            base_scale=0.0049,
            decay=0.66,
            separation_gain=1.48,
            smoothness_gain=1.18,
            abel_gain=1.20,
            epsilon_gain=1.16,
        ),
        ProfileSpec(
            name="good_epsilon_absorbed",
            family="good",
            description="Gradient leakage is routed into epsilon absorption.",
            expected_good=True,
            base_scale=0.0044,
            decay=0.67,
            separation_gain=1.25,
            smoothness_gain=1.30,
            abel_gain=1.34,
            epsilon_gain=1.50,
        ),
        *[
            ProfileSpec(
                name=f"bad_{component}_blocker",
                family="bad_blocker",
                description=f"Persistent {component.replace('_', ' ')} obstruction.",
                expected_good=False,
                base_scale=0.0029,
                decay=0.70,
                separation_gain=1.12,
                smoothness_gain=1.10,
                abel_gain=1.10,
                epsilon_gain=1.08,
                blocker=component,
            )
            for component in COMPONENTS
        ],
    ]


def sweep_regimes(count: int) -> list[SweepRegime]:
    regimes: list[SweepRegime] = []
    center = (count - 1) / 2.0
    for sweep in range(count):
        offset = (sweep - center) / max(center, 1.0)
        tolerance = 0.0088 + 0.0012 * math.cos(0.75 * sweep)
        bad_floor = 0.027 + 0.004 * math.sin(0.55 * sweep + 0.2)
        annular_separation = 1.22 + 0.18 * offset
        smoothness_gain = 1.24 + 0.16 * math.cos(0.48 * sweep + 0.4)
        epsilon_absorption = 1.05 + 0.20 * math.sin(0.63 * sweep + 0.7)
        stable = (
            0.0074 <= tolerance <= 0.0104
            and 0.022 <= bad_floor <= 0.034
            and 1.02 <= annular_separation <= 1.44
            and 1.05 <= smoothness_gain <= 1.45
            and 0.86 <= epsilon_absorption <= 1.30
        )
        regimes.append(
            SweepRegime(
                name=f"sweep_{sweep:02d}",
                sweep=sweep,
                tolerance=tolerance,
                bad_floor=bad_floor,
                annular_separation=annular_separation,
                smoothness_gain=smoothness_gain,
                epsilon_absorption=epsilon_absorption,
                stable_range=stable,
            )
        )
    return regimes


def component_weight(component: str) -> float:
    return 0.80 + 0.075 * (COMPONENTS.index(component) + 1)


def component_gain(component: str, spec: ProfileSpec, regime: SweepRegime) -> float:
    separation = spec.separation_gain * regime.annular_separation
    smoothness = spec.smoothness_gain * regime.smoothness_gain
    epsilon = spec.epsilon_gain * regime.epsilon_absorption
    if component == "cutoff_riesz_commutator":
        return smoothness
    if component == "local_calderon_zygmund_core":
        return 1.10 * smoothness
    if component == "harmonic_tail":
        return separation
    if component == "pressure_tail":
        return 0.95 * separation
    if component == "annular_cutoff":
        return math.sqrt(separation * smoothness)
    if component == "epsilon_gradient_absorption":
        return 1.20 * epsilon
    if component == "abel_recenter_lower_order":
        return spec.abel_gain * (0.92 + 0.08 * regime.epsilon_absorption)
    raise KeyError(component)


def perturbation(component: str, level: int, regime: SweepRegime, spec: ProfileSpec) -> float:
    index = COMPONENTS.index(component) + 1
    phase = 0.41 * level + 0.37 * regime.sweep + 0.19 * index
    family_shift = 0.11 if spec.expected_good else 0.27
    return 1.0 + 0.030 * math.sin(phase + family_shift)


def good_error(component: str, spec: ProfileSpec, regime: SweepRegime, level: int) -> float:
    dyadic = 2.0 ** (-(level + 1))
    polynomial = (level + 1.0) ** -1.03
    decay = spec.decay**level
    moment_power = 0.18
    if component == "local_calderon_zygmund_core":
        moment_power = 0.055
    if component == "epsilon_gradient_absorption":
        moment_power = 0.13
    base = spec.base_scale * component_weight(component) * polynomial * decay
    return (
        base
        * dyadic**moment_power
        * perturbation(component, level, regime, spec)
        / component_gain(component, spec, regime)
    )


def component_errors(
    spec: ProfileSpec, regime: SweepRegime, level: int
) -> dict[str, float]:
    errors = {
        component: good_error(component, spec, regime, level)
        for component in COMPONENTS
    }
    if spec.blocker is not None:
        blocker_index = COMPONENTS.index(spec.blocker) + 1
        sensitivity = 1.04 + 0.035 * math.sin(0.39 * level + 0.57 * regime.sweep)
        floor = regime.bad_floor * sensitivity
        floor += 0.0038 / math.sqrt(level + blocker_index)
        if spec.blocker == "epsilon_gradient_absorption":
            floor *= 1.0 + 0.09 / max(regime.epsilon_absorption, EPS)
        if spec.blocker in {"harmonic_tail", "pressure_tail", "annular_cutoff"}:
            floor *= 1.0 + 0.05 / max(regime.annular_separation, EPS)
        if spec.blocker in {"cutoff_riesz_commutator", "local_calderon_zygmund_core"}:
            floor *= 1.0 + 0.04 / max(regime.smoothness_gain, EPS)
        errors[spec.blocker] = max(errors[spec.blocker], floor)
    return errors


def combined_error(errors: dict[str, float]) -> float:
    return max(abs(value) for value in errors.values())


def build_rows(args: argparse.Namespace) -> tuple[list[SensitivityRow], list[SweepRegime]]:
    validate_args(args)
    regimes = sweep_regimes(args.sweeps)
    rows: list[SensitivityRow] = []
    for regime in regimes:
        for spec in profile_specs():
            for level in range(args.levels):
                errors = component_errors(spec, regime, level)
                combined = combined_error(errors)
                blocker = max(errors, key=errors.get)
                rows.append(
                    SensitivityRow(
                        regime=regime.name,
                        sweep=regime.sweep,
                        profile=spec.name,
                        family=spec.family,
                        level=level,
                        tolerance=regime.tolerance,
                        bad_floor=regime.bad_floor,
                        annular_separation=regime.annular_separation,
                        smoothness_gain=regime.smoothness_gain,
                        epsilon_absorption=regime.epsilon_absorption,
                        component_errors=errors,
                        combined_error=combined,
                        blocking_component=blocker if combined > regime.tolerance else None,
                        within_tolerance=combined <= regime.tolerance,
                    )
                )
    return rows, regimes


def summarize_cases(
    rows: Sequence[SensitivityRow], regimes: Sequence[SweepRegime]
) -> list[CaseSummary]:
    specs = {spec.name: spec for spec in profile_specs()}
    stable_names = {regime.name for regime in regimes if regime.stable_range}
    summaries: list[CaseSummary] = []
    for name in sorted(specs):
        spec = specs[name]
        profile_rows = [row for row in rows if row.profile == name]
        stable_rows = [row for row in profile_rows if row.regime in stable_names]
        if not stable_rows:
            raise ValueError("sensitivity sweep produced no stable regimes")
        observed_pass = all(row.within_tolerance for row in profile_rows)
        stable_pass = all(row.within_tolerance for row in stable_rows)
        worst = max(stable_rows, key=lambda row: row.combined_error)
        last_stable = sorted(stable_rows, key=lambda row: (row.sweep, row.level))[-1]
        final_components = last_stable.component_errors
        blocker_values: list[float] = []
        if spec.blocker is not None:
            blocker_values = [row.component_errors[spec.blocker] for row in stable_rows]
        expected_observed = stable_pass if spec.expected_good else not stable_pass
        summaries.append(
            CaseSummary(
                profile=name,
                family=spec.family,
                expected_good=spec.expected_good,
                observed_pass=observed_pass,
                stable_regime_pass=stable_pass,
                classification="pass" if stable_pass else "fail",
                blocker=spec.blocker,
                row_count=len(profile_rows),
                regime_count=len({row.regime for row in profile_rows}),
                max_combined_error=max(row.combined_error for row in profile_rows),
                max_stable_combined_error=worst.combined_error,
                min_bad_blocker_error=min(blocker_values) if blocker_values else None,
                final_stable_combined_error=last_stable.combined_error,
                worst_regime=worst.regime,
                final_component_errors=final_components,
                checks={
                    "expected_stable_outcome_observed": expected_observed,
                    "good_stable_below_tolerance": stable_pass if spec.expected_good else True,
                    "bad_stable_blocker_visible": (not stable_pass) if not spec.expected_good else True,
                    "declared_blocker_is_worst_component": (
                        spec.blocker is None
                        or max(final_components, key=final_components.get) == spec.blocker
                    ),
                    "finite_nonnegative_errors": all(
                        math.isfinite(row.combined_error)
                        and row.combined_error >= 0.0
                        and all(
                            math.isfinite(value) and value >= 0.0
                            for value in row.component_errors.values()
                        )
                        for row in profile_rows
                    ),
                },
            )
        )
    return summaries


def summarize_components(
    rows: Sequence[SensitivityRow], regimes: Sequence[SweepRegime]
) -> list[ComponentSensitivity]:
    stable_names = {regime.name for regime in regimes if regime.stable_range}
    stable_rows = [row for row in rows if row.regime in stable_names]
    summaries: list[ComponentSensitivity] = []
    for component in COMPONENTS:
        good_values = [
            row.component_errors[component]
            for row in stable_rows
            if row.family == "good"
        ]
        blocker_values = [
            row.component_errors[component]
            for row in stable_rows
            if row.profile == f"bad_{component}_blocker"
        ]
        non_blocker_bad = [
            row.component_errors[component]
            for row in stable_rows
            if row.family == "bad_blocker"
            and row.profile != f"bad_{component}_blocker"
        ]
        blocker_visible = [
            row
            for row in stable_rows
            if row.profile == f"bad_{component}_blocker"
            and row.component_errors[component] > row.tolerance
        ]
        max_good = max(good_values)
        min_blocker = min(blocker_values)
        max_non_blocker = max(non_blocker_bad)
        all_values = good_values + blocker_values + non_blocker_bad
        summaries.append(
            ComponentSensitivity(
                component=component,
                max_good_stable_error=max_good,
                min_bad_blocker_stable_error=min_blocker,
                max_bad_non_blocker_stable_error=max_non_blocker,
                sensitivity_span=max(all_values) - min(all_values),
                visible_blocker_regimes=len({row.regime for row in blocker_visible}),
                checks={
                    "good_component_below_stable_tolerance": all(
                        row.component_errors[component] <= row.tolerance
                        for row in stable_rows
                        if row.family == "good"
                    ),
                    "bad_blocker_above_stable_floor": all(
                        row.component_errors[component] >= row.bad_floor
                        for row in stable_rows
                        if row.profile == f"bad_{component}_blocker"
                    ),
                    "blocker_dominates_non_blocker_bad": min_blocker > max_non_blocker,
                    "finite_nonnegative_span": math.isfinite(max_good)
                    and math.isfinite(min_blocker)
                    and math.isfinite(max_non_blocker)
                    and max_good >= 0.0
                    and min_blocker >= 0.0
                    and max_non_blocker >= 0.0,
                },
            )
        )
    return summaries


def compact_rows(rows: Sequence[SensitivityRow]) -> list[dict[str, object]]:
    return [
        {
            "regime": row.regime,
            "sweep": row.sweep,
            "profile": row.profile,
            "family": row.family,
            "level": row.level,
            "combined_error": row.combined_error,
            "tolerance": row.tolerance,
            "bad_floor": row.bad_floor,
            "annular_separation": row.annular_separation,
            "smoothness_gain": row.smoothness_gain,
            "epsilon_absorption": row.epsilon_absorption,
            "blocking_component": row.blocking_component,
            "within_tolerance": row.within_tolerance,
            "component_errors": row.component_errors,
        }
        for row in rows
    ]


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    rows, regimes = build_rows(args)
    case_summaries = summarize_cases(rows, regimes)
    component_summaries = summarize_components(rows, regimes)
    good_cases = [summary for summary in case_summaries if summary.expected_good]
    bad_cases = [summary for summary in case_summaries if not summary.expected_good]

    stable_regimes = [regime for regime in regimes if regime.stable_range]
    good_stable = all(summary.stable_regime_pass for summary in good_cases)
    bad_visible = all(not summary.stable_regime_pass for summary in bad_cases)
    expected = all(
        summary.checks["expected_stable_outcome_observed"]
        for summary in case_summaries
    )
    blocker_dominance = all(
        summary.checks["declared_blocker_is_worst_component"]
        for summary in bad_cases
    )
    component_checks = all(
        all(value for value in summary.checks.values())
        for summary in component_summaries
    )
    finite_nonnegative = all(
        summary.checks["finite_nonnegative_errors"] for summary in case_summaries
    )
    stable_range_present = len(stable_regimes) >= max(3, args.sweeps // 2)

    validation_flags = {
        "stable_range_present": stable_range_present,
        "good_profiles_stable_below_tolerance": good_stable,
        "bad_blockers_stable_visible": bad_visible,
        "expected_stable_outcomes_observed": expected,
        "blocker_components_dominate_bad_profiles": blocker_dominance,
        "component_sensitivity_checks_pass": component_checks,
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
        "profile_count": len(case_summaries),
        "good_profile_count": len(good_cases),
        "bad_profile_count": len(bad_cases),
        "component_count": len(COMPONENTS),
        "sweep_count": len(regimes),
        "stable_sweep_count": len(stable_regimes),
        "row_count": len(rows),
        "max_good_stable_error": max(
            summary.max_stable_combined_error for summary in good_cases
        ),
        "max_good_stable_tolerance_fraction": max(
            row.combined_error / max(row.tolerance, EPS)
            for row in rows
            if row.family == "good"
            and any(regime.name == row.regime and regime.stable_range for regime in regimes)
        ),
        "min_bad_blocker_stable_floor_fraction": min(
            row.combined_error / max(row.bad_floor, EPS)
            for row in rows
            if row.family == "bad_blocker"
            and any(regime.name == row.regime and regime.stable_range for regime in regimes)
        ),
        "min_bad_stable_error": min(
            summary.max_stable_combined_error for summary in bad_cases
        ),
        "max_component_sensitivity_span": max(
            summary.sensitivity_span for summary in component_summaries
        ),
    }

    return {
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": {
            "levels": args.levels,
            "sweeps": args.sweeps,
            "components": list(COMPONENTS),
            "varied_parameters": [
                "tolerance",
                "bad_floor",
                "annular_separation",
                "smoothness_gain",
                "epsilon_absorption",
            ],
        },
        "regimes": [asdict(regime) for regime in regimes],
        "good_bad_summaries": {
            "good": [asdict(summary) for summary in good_cases],
            "bad": [asdict(summary) for summary in bad_cases],
        },
        "component_sensitivity": [
            asdict(summary) for summary in component_summaries
        ],
        "aggregate_metrics": aggregate_metrics,
        "validation_flags": validation_flags,
        "rows": compact_rows(rows),
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
