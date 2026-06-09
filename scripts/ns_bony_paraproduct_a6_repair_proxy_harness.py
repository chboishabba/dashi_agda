#!/usr/bin/env python3
"""NS A6.2 Bony paraproduct repair proxy harness.

This deterministic pure-stdlib diagnostic models the corrected A6.2 repair:

    naive same-shell strain localization fails on off-shell tails with O(1)
    error, while the Bony decomposition separates:

      * low-high paraproduct exactness,
      * finitely many resonant shells,
      * decaying high-frequency strain tail,
      * O(1/N) Abel aggregate error.

Good profiles keep the corrected Bony checks below tolerance even though the
naive same-shell off-shell tail remains O(1).  Bad profiles preserve exactly
one corrected obstruction.  This is bookkeeping only: it proves no Bony
paraproduct theorem, no A6 identity, no Navier-Stokes regularity result, and no
Clay claim.  The emitted payload always has promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


DEFAULT_OUTPUT = Path("outputs/ns_bony_paraproduct_a6_repair_proxy_harness.json")
EXACTNESS_TOLERANCE = 1.0e-12
MAX_RESONANT_COUNT = 5

CORRECTED_COMPONENTS = (
    "paraproduct_exactness",
    "resonant_count",
    "high_frequency_decay",
    "aggregate_o1_over_n",
)


@dataclass(frozen=True)
class SweepRegime:
    name: str
    sweep: int
    corrected_tolerance: float
    naive_tail_floor: float
    high_tail_gain: float
    aggregate_constant: float
    stable_range: bool


@dataclass(frozen=True)
class ProfileSpec:
    name: str
    family: str
    expected_pass: bool
    description: str
    paraproduct_exact: bool
    resonant_count_base: int
    high_tail_power: float
    aggregate_power: float
    naive_tail_scale: float
    blocker: str | None = None


@dataclass(frozen=True)
class BonyRepairRow:
    regime: str
    sweep: int
    profile: str
    family: str
    level: int
    effective_n: int
    expected_pass: bool
    naive_same_shell_offshell_error: float
    corrected_component_errors: dict[str, float]
    paraproduct_exactness_error: float
    resonant_shell_count: int
    high_frequency_tail_error: float
    aggregate_error: float
    corrected_tolerance: float
    naive_tail_floor: float
    aggregate_bound: float
    passed_proxy_checks: bool
    checks: dict[str, bool]
    failure_reasons: list[str]


@dataclass(frozen=True)
class ProfileSummary:
    profile: str
    family: str
    expected_pass: bool
    blocker: str | None
    row_count: int
    rows_passing: int
    rows_failing: int
    max_naive_same_shell_error: float
    min_naive_same_shell_error: float
    max_paraproduct_exactness_error: float
    max_resonant_shell_count: int
    max_high_frequency_tail_error: float
    max_aggregate_error: float
    min_aggregate_bound: float
    classification_matches_expectation: bool
    checks: dict[str, bool]


@dataclass(frozen=True)
class ComponentSummary:
    component: str
    max_good_error: float
    min_bad_blocker_error: float | None
    separation_margin: float | None
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", type=int, default=12)
    parser.add_argument("--sweeps", type=int, default=8)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.levels < 8:
        raise ValueError("--levels must be at least 8")
    if args.sweeps < 4:
        raise ValueError("--sweeps must be at least 4")


def sweep_regimes(count: int) -> list[SweepRegime]:
    regimes: list[SweepRegime] = []
    center = (count - 1) / 2.0
    for sweep in range(count):
        offset = (sweep - center) / max(center, 1.0)
        corrected_tolerance = 0.046 + 0.004 * math.cos(0.53 * sweep + 0.2)
        naive_tail_floor = 0.245 + 0.018 * math.sin(0.47 * sweep + 0.3)
        high_tail_gain = 0.82 + 0.09 * math.cos(0.41 * sweep)
        aggregate_constant = 0.44 + 0.025 * math.sin(0.61 * sweep + 0.1)
        stable = (
            0.040 <= corrected_tolerance <= 0.051
            and 0.225 <= naive_tail_floor <= 0.270
            and 0.72 <= high_tail_gain <= 0.92
            and 0.40 <= aggregate_constant <= 0.48
            and abs(offset) <= 1.0
        )
        regimes.append(
            SweepRegime(
                name=f"sweep_{sweep:02d}",
                sweep=sweep,
                corrected_tolerance=corrected_tolerance,
                naive_tail_floor=naive_tail_floor,
                high_tail_gain=high_tail_gain,
                aggregate_constant=aggregate_constant,
                stable_range=stable,
            )
        )
    return regimes


def profile_specs() -> list[ProfileSpec]:
    return [
        ProfileSpec(
            name="good_bony_low_high_exact",
            family="good_bony_repair",
            expected_pass=True,
            description="Low-high paraproduct is exactly localized; resonant shells are finite.",
            paraproduct_exact=True,
            resonant_count_base=5,
            high_tail_power=1.22,
            aggregate_power=1.18,
            naive_tail_scale=1.02,
        ),
        ProfileSpec(
            name="good_bony_resonant_buffered",
            family="good_bony_repair",
            expected_pass=True,
            description="Near-diagonal resonant band is bounded by the five-shell budget.",
            paraproduct_exact=True,
            resonant_count_base=4,
            high_tail_power=1.35,
            aggregate_power=1.10,
            naive_tail_scale=1.07,
        ),
        ProfileSpec(
            name="good_bony_high_tail_absorbed",
            family="good_bony_repair",
            expected_pass=True,
            description="High-frequency strain tail decays faster than the Abel O(1/N) budget.",
            paraproduct_exact=True,
            resonant_count_base=5,
            high_tail_power=1.55,
            aggregate_power=1.24,
            naive_tail_scale=0.98,
        ),
        ProfileSpec(
            name="bad_naive_same_shell_tail_unrepaired",
            family="bad_corrected_obstruction",
            expected_pass=False,
            description="Keeps the O(1) off-shell tail inside the corrected aggregate.",
            paraproduct_exact=True,
            resonant_count_base=5,
            high_tail_power=1.20,
            aggregate_power=0.0,
            naive_tail_scale=1.16,
            blocker="aggregate_o1_over_n",
        ),
        ProfileSpec(
            name="bad_paraproduct_not_exact",
            family="bad_corrected_obstruction",
            expected_pass=False,
            description="Paraproduct localization has a persistent nonzero exactness defect.",
            paraproduct_exact=False,
            resonant_count_base=5,
            high_tail_power=1.25,
            aggregate_power=1.15,
            naive_tail_scale=1.03,
            blocker="paraproduct_exactness",
        ),
        ProfileSpec(
            name="bad_resonant_band_unbounded",
            family="bad_corrected_obstruction",
            expected_pass=False,
            description="Near-diagonal resonant band grows beyond the five-shell Bony budget.",
            paraproduct_exact=True,
            resonant_count_base=7,
            high_tail_power=1.30,
            aggregate_power=1.15,
            naive_tail_scale=1.01,
            blocker="resonant_count",
        ),
        ProfileSpec(
            name="bad_high_frequency_tail_no_decay",
            family="bad_corrected_obstruction",
            expected_pass=False,
            description="High-frequency strain tail remains visible instead of decaying.",
            paraproduct_exact=True,
            resonant_count_base=5,
            high_tail_power=0.0,
            aggregate_power=1.15,
            naive_tail_scale=1.04,
            blocker="high_frequency_decay",
        ),
    ]


def deterministic_ripple(*, level: int, sweep: int, phase: float) -> float:
    return 1.0 + 0.022 * math.sin(0.43 * level + 0.71 * sweep + phase)


def naive_same_shell_error(spec: ProfileSpec, regime: SweepRegime, level: int) -> float:
    return (
        regime.naive_tail_floor
        * 1.065
        * spec.naive_tail_scale
        * deterministic_ripple(level=level, sweep=regime.sweep, phase=0.2)
    )


def paraproduct_error(spec: ProfileSpec, regime: SweepRegime, level: int) -> float:
    if spec.paraproduct_exact:
        return 0.0
    return (
        0.083
        + 0.006 / math.sqrt(level + 1.0)
        + 0.002 * math.sin(0.37 * regime.sweep + 0.13 * level)
    )


def resonant_shell_count(spec: ProfileSpec, regime: SweepRegime, level: int) -> int:
    if spec.blocker == "resonant_count":
        return spec.resonant_count_base + (1 if (level + regime.sweep) % 3 == 0 else 0)
    return spec.resonant_count_base


def high_frequency_tail(spec: ProfileSpec, regime: SweepRegime, level: int) -> float:
    if spec.blocker == "high_frequency_decay":
        return (
            0.071
            + 0.004 * math.sin(0.19 * level + 0.61 * regime.sweep)
        )
    return (
        0.235
        * regime.high_tail_gain
        / ((level + 1.0) ** spec.high_tail_power)
        * deterministic_ripple(level=level, sweep=regime.sweep, phase=1.1)
    )


def aggregate_error(
    *,
    spec: ProfileSpec,
    regime: SweepRegime,
    level: int,
    paraproduct: float,
    high_tail: float,
    resonant_count_value: int,
) -> float:
    if spec.blocker == "aggregate_o1_over_n":
        return naive_same_shell_error(spec, regime, level) + 0.012

    resonant_budget = 0.018 * resonant_count_value / float(level + 1) ** 1.45
    abel_budget = (
        regime.aggregate_constant
        / float(level + 1) ** spec.aggregate_power
        * 0.58
        * deterministic_ripple(level=level, sweep=regime.sweep, phase=2.1)
    )
    return paraproduct + high_tail + resonant_budget + abel_budget


def corrected_component_errors(
    *,
    paraproduct: float,
    resonant_count_value: int,
    high_tail: float,
    aggregate: float,
    aggregate_bound: float,
) -> dict[str, float]:
    count_excess = max(0.0, float(resonant_count_value - MAX_RESONANT_COUNT))
    aggregate_excess = max(0.0, aggregate - aggregate_bound)
    return {
        "paraproduct_exactness": paraproduct,
        "resonant_count": count_excess,
        "high_frequency_decay": high_tail,
        "aggregate_o1_over_n": aggregate_excess,
    }


def build_rows(args: argparse.Namespace) -> tuple[list[BonyRepairRow], list[SweepRegime]]:
    validate_args(args)
    regimes = sweep_regimes(args.sweeps)
    rows: list[BonyRepairRow] = []
    for regime in regimes:
        for spec in profile_specs():
            for level in range(8, args.levels + 1):
                effective_n = level + 1
                naive_error = naive_same_shell_error(spec, regime, level)
                p_error = paraproduct_error(spec, regime, level)
                resonant = resonant_shell_count(spec, regime, level)
                high_tail = high_frequency_tail(spec, regime, level)
                aggregate_bound = regime.aggregate_constant / float(effective_n)
                aggregate = aggregate_error(
                    spec=spec,
                    regime=regime,
                    level=level,
                    paraproduct=p_error,
                    high_tail=high_tail,
                    resonant_count_value=resonant,
                )
                components = corrected_component_errors(
                    paraproduct=p_error,
                    resonant_count_value=resonant,
                    high_tail=high_tail,
                    aggregate=aggregate,
                    aggregate_bound=aggregate_bound,
                )
                checks = {
                    "naive_same_shell_offshell_tail_is_o1": naive_error >= regime.naive_tail_floor,
                    "paraproduct_exact": p_error <= EXACTNESS_TOLERANCE,
                    "resonant_band_finite": resonant <= MAX_RESONANT_COUNT,
                    "high_frequency_tail_below_corrected_tolerance": high_tail <= regime.corrected_tolerance,
                    "aggregate_error_o1_over_n": aggregate <= aggregate_bound,
                    "finite_nonnegative_values": all(
                        math.isfinite(value) and value >= 0.0
                        for value in [naive_error, p_error, high_tail, aggregate, aggregate_bound]
                    ),
                }
                passed = all(checks.values())
                rows.append(
                    BonyRepairRow(
                        regime=regime.name,
                        sweep=regime.sweep,
                        profile=spec.name,
                        family=spec.family,
                        level=level,
                        effective_n=effective_n,
                        expected_pass=spec.expected_pass,
                        naive_same_shell_offshell_error=naive_error,
                        corrected_component_errors=components,
                        paraproduct_exactness_error=p_error,
                        resonant_shell_count=resonant,
                        high_frequency_tail_error=high_tail,
                        aggregate_error=aggregate,
                        corrected_tolerance=regime.corrected_tolerance,
                        naive_tail_floor=regime.naive_tail_floor,
                        aggregate_bound=aggregate_bound,
                        passed_proxy_checks=passed,
                        checks=checks,
                        failure_reasons=[name for name, ok in checks.items() if not ok],
                    )
                )
    return rows, regimes


def summarize_profiles(rows: Sequence[BonyRepairRow]) -> list[ProfileSummary]:
    summaries: list[ProfileSummary] = []
    specs = {spec.name: spec for spec in profile_specs()}
    for name in sorted(specs):
        spec = specs[name]
        selected = [row for row in rows if row.profile == name]
        if not selected:
            raise ValueError(f"no rows for profile {name}")
        rows_passing = sum(1 for row in selected if row.passed_proxy_checks)
        rows_failing = len(selected) - rows_passing
        observed_pass = rows_failing == 0
        summaries.append(
            ProfileSummary(
                profile=name,
                family=spec.family,
                expected_pass=spec.expected_pass,
                blocker=spec.blocker,
                row_count=len(selected),
                rows_passing=rows_passing,
                rows_failing=rows_failing,
                max_naive_same_shell_error=max(
                    row.naive_same_shell_offshell_error for row in selected
                ),
                min_naive_same_shell_error=min(
                    row.naive_same_shell_offshell_error for row in selected
                ),
                max_paraproduct_exactness_error=max(
                    row.paraproduct_exactness_error for row in selected
                ),
                max_resonant_shell_count=max(row.resonant_shell_count for row in selected),
                max_high_frequency_tail_error=max(
                    row.high_frequency_tail_error for row in selected
                ),
                max_aggregate_error=max(row.aggregate_error for row in selected),
                min_aggregate_bound=min(row.aggregate_bound for row in selected),
                classification_matches_expectation=observed_pass == spec.expected_pass,
                checks={
                    "expected_classification_observed": observed_pass == spec.expected_pass,
                    "naive_tail_is_o1_in_every_row": all(
                        row.checks["naive_same_shell_offshell_tail_is_o1"]
                        for row in selected
                    ),
                    "good_profiles_all_pass": observed_pass if spec.expected_pass else True,
                    "bad_profiles_all_fail": (not observed_pass) if not spec.expected_pass else True,
                    "declared_blocker_visible": (
                        True
                        if spec.blocker is None
                        else all(spec.blocker in row.failure_reasons for row in selected)
                    ),
                },
            )
        )
    return summaries


def summarize_components(rows: Sequence[BonyRepairRow]) -> list[ComponentSummary]:
    summaries: list[ComponentSummary] = []
    for component in CORRECTED_COMPONENTS:
        good_values = [
            row.corrected_component_errors[component]
            for row in rows
            if row.expected_pass
        ]
        blocker_values = [
            row.corrected_component_errors[component]
            for row in rows
            if any(spec.name == row.profile and spec.blocker == component for spec in profile_specs())
        ]
        max_good = max(good_values)
        min_blocker = min(blocker_values) if blocker_values else None
        margin = None if min_blocker is None else min_blocker - max_good
        summaries.append(
            ComponentSummary(
                component=component,
                max_good_error=max_good,
                min_bad_blocker_error=min_blocker,
                separation_margin=margin,
                checks={
                    "good_component_finite": all(
                        math.isfinite(value) and value >= 0.0 for value in good_values
                    ),
                    "blocker_component_present": min_blocker is not None,
                    "blocker_separates_from_good": (
                        True if margin is None else margin > 0.0
                    ),
                },
            )
        )
    return summaries


def aggregate_metrics(rows: Sequence[BonyRepairRow]) -> dict[str, Any]:
    good = [row for row in rows if row.expected_pass]
    bad = [row for row in rows if not row.expected_pass]
    return {
        "row_count": len(rows),
        "good_row_count": len(good),
        "bad_row_count": len(bad),
        "good_rows_passed": sum(1 for row in good if row.passed_proxy_checks),
        "bad_rows_failed": sum(1 for row in bad if not row.passed_proxy_checks),
        "classification_accuracy": sum(
            1 for row in rows if row.passed_proxy_checks == row.expected_pass
        )
        / float(len(rows)),
        "min_naive_same_shell_offshell_error": min(
            row.naive_same_shell_offshell_error for row in rows
        ),
        "max_good_paraproduct_exactness_error": max(
            row.paraproduct_exactness_error for row in good
        ),
        "max_good_resonant_shell_count": max(row.resonant_shell_count for row in good),
        "max_good_high_frequency_tail_error": max(
            row.high_frequency_tail_error for row in good
        ),
        "max_good_aggregate_error": max(row.aggregate_error for row in good),
        "min_good_aggregate_bound": min(row.aggregate_bound for row in good),
        "min_bad_aggregate_error": min(row.aggregate_error for row in bad),
    }


def compact_rows(rows: Sequence[BonyRepairRow]) -> list[dict[str, Any]]:
    return [
        {
            "regime": row.regime,
            "sweep": row.sweep,
            "profile": row.profile,
            "family": row.family,
            "level": row.level,
            "effective_n": row.effective_n,
            "expected_pass": row.expected_pass,
            "passed_proxy_checks": row.passed_proxy_checks,
            "naive_same_shell_offshell_error": row.naive_same_shell_offshell_error,
            "paraproduct_exactness_error": row.paraproduct_exactness_error,
            "resonant_shell_count": row.resonant_shell_count,
            "high_frequency_tail_error": row.high_frequency_tail_error,
            "aggregate_error": row.aggregate_error,
            "aggregate_bound": row.aggregate_bound,
            "failure_reasons": row.failure_reasons,
        }
        for row in rows
    ]


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    rows, regimes = build_rows(args)
    profile_summaries = summarize_profiles(rows)
    component_summaries = summarize_components(rows)
    metrics = aggregate_metrics(rows)
    good_profiles = [summary for summary in profile_summaries if summary.expected_pass]
    bad_profiles = [summary for summary in profile_summaries if not summary.expected_pass]
    validation_flags = {
        "all_good_profiles_pass": all(summary.rows_failing == 0 for summary in good_profiles),
        "all_bad_profiles_fail": all(summary.rows_passing == 0 for summary in bad_profiles),
        "classification_matches_expectation": metrics["classification_accuracy"] == 1.0,
        "naive_same_shell_tail_o1_visible": metrics[
            "min_naive_same_shell_offshell_error"
        ]
        >= min(regime.naive_tail_floor for regime in regimes),
        "bony_paraproduct_exact_for_good_profiles": metrics[
            "max_good_paraproduct_exactness_error"
        ]
        <= EXACTNESS_TOLERANCE,
        "resonant_count_finite_for_good_profiles": metrics[
            "max_good_resonant_shell_count"
        ]
        <= MAX_RESONANT_COUNT,
        "high_frequency_decay_for_good_profiles": all(
            row.high_frequency_tail_error <= row.corrected_tolerance
            for row in rows
            if row.expected_pass
        ),
        "aggregate_o1_over_n_for_good_profiles": all(
            row.aggregate_error <= row.aggregate_bound
            for row in rows
            if row.expected_pass
        ),
        "bad_naive_unrepaired_profile_present": any(
            row.profile == "bad_naive_same_shell_tail_unrepaired" for row in rows
        ),
        "bad_paraproduct_profile_present": any(
            row.profile == "bad_paraproduct_not_exact" for row in rows
        ),
        "bad_resonant_profile_present": any(
            row.profile == "bad_resonant_band_unbounded" for row in rows
        ),
        "bad_high_tail_profile_present": any(
            row.profile == "bad_high_frequency_tail_no_decay" for row in rows
        ),
        "stdlib_only": True,
        "deterministic": True,
        "diagnostic_only": True,
        "promotion_blocked": True,
    }
    payload: dict[str, Any] = {
        "ok": all(validation_flags.values()),
        "promotion": False,
        "diagnostic_only": True,
        "claim_scope": "corrected A6.2 Bony paraproduct repair diagnostic proxy only",
        "parameters": {
            "levels": args.levels,
            "sweeps": args.sweeps,
            "exactness_tolerance": EXACTNESS_TOLERANCE,
            "max_resonant_count": MAX_RESONANT_COUNT,
        },
        "validation_flags": validation_flags,
        "aggregate": metrics,
        "regimes": [asdict(regime) for regime in regimes],
        "profile_summaries": [asdict(summary) for summary in profile_summaries],
        "component_summaries": [asdict(summary) for summary in component_summaries],
        "rows": compact_rows(rows),
    }
    return payload


def write_payload(payload: dict[str, Any], output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = build_payload(args)
    write_payload(payload, args.json_output)
    if args.json:
        print(
            json.dumps(
                {
                    "ok": payload["ok"],
                    "promotion": payload["promotion"],
                    "diagnostic_only": payload["diagnostic_only"],
                    "aggregate": payload["aggregate"],
                    "validation_flags": payload["validation_flags"],
                    "output": str(args.json_output),
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        status = "ok" if payload["ok"] else "failed"
        print(f"{status}: wrote {args.json_output}")
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
