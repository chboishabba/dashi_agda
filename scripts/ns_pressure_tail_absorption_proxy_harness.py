#!/usr/bin/env python3
"""NS pressure-tail absorption proxy harness.

This pure-stdlib diagnostic evaluates synthetic radial profiles against a
finite pressure-tail absorption budget.  It tracks three proxy channels:

  * pressure tail outside the localization cutoff
  * cutoff/pressure commutator concentrated on the transition annulus
  * nonabsorbed gradient residual

Good profiles are compact, Schwartz, or annular with decaying packet mass, so
refinement drives all channels below tolerance.  Bad profiles retain a harmonic
tail, an annular plateau, or a nonabsorbed gradient residual and are expected to
fail.  This is diagnostic bookkeeping only; it proves no Navier-Stokes theorem
and always emits promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


DEFAULT_OUTPUT = Path("outputs/ns_pressure_tail_absorption_proxy_harness.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class ProfileSpec:
    name: str
    family: str
    description: str
    expected_good: bool
    amplitude: Callable[[float, int], float]
    gradient: Callable[[float, int], float]


@dataclass(frozen=True)
class DepthRow:
    profile: str
    family: str
    depth: int
    cutoff_radius: float
    transition_width: float
    pressure_tail_error: float
    commutator_error: float
    gradient_residual_error: float
    combined_error: float
    tolerance: float
    within_tolerance: bool


@dataclass(frozen=True)
class ProfileSummary:
    name: str
    family: str
    description: str
    expected_good: bool
    observed_pass: bool
    classification: str
    row_count: int
    initial_combined_error: float
    final_combined_error: float
    decay_ratio: float
    max_combined_error: float
    min_combined_error: float
    final_pressure_tail_error: float
    final_commutator_error: float
    final_gradient_residual_error: float
    rows_within_tolerance: int
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", type=int, default=14, help="Number of refinement depths.")
    parser.add_argument("--radius-max", type=float, default=72.0, help="Outer quadrature radius.")
    parser.add_argument("--samples", type=int, default=2400, help="Radial quadrature samples.")
    parser.add_argument("--base-cutoff-radius", type=float, default=2.5)
    parser.add_argument("--cutoff-step", type=float, default=2.6)
    parser.add_argument("--transition-width", type=float, default=1.15)
    parser.add_argument("--tolerance", type=float, default=8.0e-3)
    parser.add_argument("--good-decay-ratio", type=float, default=0.08)
    parser.add_argument("--bad-floor", type=float, default=2.5e-2)
    parser.add_argument("--pressure-weight", type=float, default=1.0)
    parser.add_argument("--commutator-weight", type=float, default=0.72)
    parser.add_argument("--gradient-weight", type=float, default=0.42)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.depths < 6:
        raise ValueError("--depths must be at least 6")
    if args.radius_max <= 8.0:
        raise ValueError("--radius-max must exceed 8")
    if args.samples < 200:
        raise ValueError("--samples must be at least 200")
    if args.base_cutoff_radius <= 0.0:
        raise ValueError("--base-cutoff-radius must be positive")
    if args.cutoff_step <= 0.0:
        raise ValueError("--cutoff-step must be positive")
    if args.transition_width <= 0.0:
        raise ValueError("--transition-width must be positive")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if not (0.0 < args.good_decay_ratio < 1.0):
        raise ValueError("--good-decay-ratio must satisfy 0 < ratio < 1")
    if args.bad_floor <= args.tolerance:
        raise ValueError("--bad-floor must be larger than --tolerance")
    final_cutoff = args.base_cutoff_radius + (args.depths - 1) * args.cutoff_step
    if final_cutoff + 4.0 * args.transition_width >= args.radius_max:
        raise ValueError("--radius-max must leave room beyond the final cutoff annulus")
    for name in ("pressure_weight", "commutator_weight", "gradient_weight"):
        if getattr(args, name) <= 0.0:
            raise ValueError(f"--{name.replace('_', '-')} must be positive")


def gaussian(r: float, center: float, width: float) -> float:
    z = (r - center) / max(width, EPS)
    return math.exp(-0.5 * z * z)


def sech2(x: float) -> float:
    c = math.cosh(max(-40.0, min(40.0, x)))
    return 1.0 / (c * c)


def smooth_step_outside(r: float, cutoff: float, width: float) -> float:
    return 0.5 * (1.0 + math.tanh((r - cutoff) / width))


def cutoff_derivative_abs(r: float, cutoff: float, width: float) -> float:
    return 0.5 * sech2((r - cutoff) / width) / width


def radial_grid(radius_max: float, samples: int) -> list[tuple[float, float]]:
    dr = radius_max / samples
    return [((index + 0.5) * dr, dr) for index in range(samples)]


def profile_specs() -> list[ProfileSpec]:
    return [
        ProfileSpec(
            name="good_compact_bump",
            family="compact",
            description="Compact radial bump supported well inside late cutoffs.",
            expected_good=True,
            amplitude=lambda r, depth: 0.30 * gaussian(r, 4.0, 1.15) if r <= 8.2 else 0.0,
            gradient=lambda r, depth: 0.19 * abs(r - 4.0) * gaussian(r, 4.0, 1.15),
        ),
        ProfileSpec(
            name="good_schwartz_tail",
            family="schwartz",
            description="Rapidly decreasing pressure source with smooth Schwartz tail.",
            expected_good=True,
            amplitude=lambda r, depth: 0.24 * math.exp(-0.055 * r * r) * (1.0 + 0.08 * math.cos(1.7 * r)),
            gradient=lambda r, depth: 0.24 * (0.11 * r + 0.14) * math.exp(-0.055 * r * r),
        ),
        ProfileSpec(
            name="good_localized_annular_tail",
            family="localized_annular_tail",
            description="Moving annular packets whose mass is absorbed by radial decay.",
            expected_good=True,
            amplitude=lambda r, depth: 0.22 * gaussian(r, 6.0, 1.0)
            + 0.34 * (1.0 + r) ** -3.65 * (1.0 + 0.12 * math.sin(0.9 * r)),
            gradient=lambda r, depth: 0.12 * gaussian(r, 6.0, 1.0) + 0.62 * (1.0 + r) ** -4.05,
        ),
        ProfileSpec(
            name="bad_persistent_harmonic_tail",
            family="persistent_harmonic_tail",
            description="Harmonic-size tail keeps pressure mass outside every tested cutoff.",
            expected_good=False,
            amplitude=lambda r, depth: 0.050 / (1.0 + r) + 0.010 * gaussian(r, 4.5, 1.6),
            gradient=lambda r, depth: 0.020 / (1.0 + r),
        ),
        ProfileSpec(
            name="bad_annular_plateau",
            family="annular_plateau",
            description="Plateau rides the cutoff annulus, keeping commutator leakage visible.",
            expected_good=False,
            amplitude=lambda r, depth: 0.030 * gaussian(r, 5.0, 1.4)
            + 0.115 * gaussian(r, 2.5 + 2.6 * depth, 1.55),
            gradient=lambda r, depth: 0.030 * gaussian(r, 5.0, 1.4)
            + 0.060 * gaussian(r, 2.5 + 2.6 * depth, 1.55),
        ),
        ProfileSpec(
            name="bad_nonabsorbed_gradient",
            family="nonabsorbed_gradient",
            description="Pressure tail decays, but a background gradient residual is not absorbed.",
            expected_good=False,
            amplitude=lambda r, depth: 0.20 * math.exp(-0.045 * r * r),
            gradient=lambda r, depth: 0.027 + 0.018 * math.exp(-0.035 * r * r),
        ),
    ]


def shell_measure(r: float) -> float:
    return 4.0 * math.pi * r * r


def compute_row(spec: ProfileSpec, depth: int, args: argparse.Namespace, grid: Sequence[tuple[float, float]]) -> DepthRow:
    cutoff = args.base_cutoff_radius + depth * args.cutoff_step
    width = args.transition_width / math.sqrt(1.0 + 0.18 * depth)
    tail_integral = 0.0
    commutator_integral = 0.0
    gradient_integral = 0.0
    total_mass = 0.0

    for r, dr in grid:
        amp = abs(spec.amplitude(r, depth))
        grad = abs(spec.gradient(r, depth))
        measure = shell_measure(r) * dr
        outside = smooth_step_outside(r, cutoff, width)
        chi_prime = cutoff_derivative_abs(r, cutoff, width)
        tail_integral += amp * outside * measure / (1.0 + r)
        commutator_integral += amp * chi_prime * measure / math.sqrt(1.0 + r)
        gradient_integral += grad * outside * measure / ((1.0 + r) ** 2.0)
        total_mass += (amp + 0.35 * grad) * measure / (1.0 + r)

    normalizer = max(total_mass, EPS)
    pressure_tail = args.pressure_weight * tail_integral / normalizer
    commutator = args.commutator_weight * commutator_integral / normalizer
    gradient_residual = args.gradient_weight * gradient_integral / normalizer
    combined = max(pressure_tail, commutator, gradient_residual)
    return DepthRow(
        profile=spec.name,
        family=spec.family,
        depth=depth,
        cutoff_radius=cutoff,
        transition_width=width,
        pressure_tail_error=pressure_tail,
        commutator_error=commutator,
        gradient_residual_error=gradient_residual,
        combined_error=combined,
        tolerance=args.tolerance,
        within_tolerance=combined <= args.tolerance,
    )


def nonincreasing_tail(rows: Sequence[DepthRow]) -> bool:
    values = [row.pressure_tail_error for row in rows]
    return all(nxt <= prev + 4.0e-4 for prev, nxt in zip(values, values[1:]))


def summarize_profile(spec: ProfileSpec, rows: Sequence[DepthRow], args: argparse.Namespace) -> ProfileSummary:
    if not rows:
        raise ValueError(f"profile {spec.name} produced no rows")
    initial = rows[0].combined_error
    final = rows[-1].combined_error
    decay_ratio = final / max(initial, EPS)
    max_error = max(row.combined_error for row in rows)
    min_error = min(row.combined_error for row in rows)
    rows_within = sum(1 for row in rows if row.within_tolerance)
    finite_nonnegative = all(
        math.isfinite(row.pressure_tail_error)
        and math.isfinite(row.commutator_error)
        and math.isfinite(row.gradient_residual_error)
        and row.pressure_tail_error >= 0.0
        and row.commutator_error >= 0.0
        and row.gradient_residual_error >= 0.0
        for row in rows
    )

    good_pass = (
        rows[-1].pressure_tail_error <= args.tolerance
        and rows[-1].commutator_error <= args.tolerance
        and rows[-1].gradient_residual_error <= args.tolerance
        and decay_ratio <= args.good_decay_ratio
    )
    bad_fails = min_error >= args.bad_floor or final > args.tolerance
    observed_pass = good_pass if spec.expected_good else not bad_fails
    if spec.expected_good and good_pass:
        classification = "good_absorbed_below_tolerance"
    elif (not spec.expected_good) and bad_fails:
        classification = "bad_obstruction_detected"
    else:
        classification = "unexpected_or_borderline"

    checks = {
        "finite_nonnegative_errors": finite_nonnegative,
        "rows_present": len(rows) == args.depths,
        "final_pressure_tail_below_tolerance": rows[-1].pressure_tail_error <= args.tolerance,
        "final_commutator_below_tolerance": rows[-1].commutator_error <= args.tolerance,
        "final_gradient_residual_below_tolerance": rows[-1].gradient_residual_error <= args.tolerance,
        "decay_ratio_below_good_threshold": decay_ratio <= args.good_decay_ratio,
        "pressure_tail_nonincreasing_up_to_quadrature_noise": nonincreasing_tail(rows),
        "bad_obstruction_above_floor_or_final_tolerance": bad_fails if not spec.expected_good else True,
        "expected_classification_met": (spec.expected_good and good_pass) or ((not spec.expected_good) and bad_fails),
        "promotion_false": True,
        "diagnostic_only": True,
    }
    return ProfileSummary(
        name=spec.name,
        family=spec.family,
        description=spec.description,
        expected_good=spec.expected_good,
        observed_pass=observed_pass,
        classification=classification,
        row_count=len(rows),
        initial_combined_error=initial,
        final_combined_error=final,
        decay_ratio=decay_ratio,
        max_combined_error=max_error,
        min_combined_error=min_error,
        final_pressure_tail_error=rows[-1].pressure_tail_error,
        final_commutator_error=rows[-1].commutator_error,
        final_gradient_residual_error=rows[-1].gradient_residual_error,
        rows_within_tolerance=rows_within,
        checks=checks,
    )


def aggregate_metrics(summaries: Sequence[ProfileSummary]) -> dict[str, float | int]:
    good = [summary for summary in summaries if summary.expected_good]
    bad = [summary for summary in summaries if not summary.expected_good]
    return {
        "good_case_count": len(good),
        "bad_case_count": len(bad),
        "good_cases_absorbed": sum(1 for summary in good if summary.classification == "good_absorbed_below_tolerance"),
        "bad_cases_rejected": sum(1 for summary in bad if summary.classification == "bad_obstruction_detected"),
        "max_good_final_combined_error": max((summary.final_combined_error for summary in good), default=0.0),
        "min_good_decay_ratio": min((summary.decay_ratio for summary in good), default=0.0),
        "max_good_decay_ratio": max((summary.decay_ratio for summary in good), default=0.0),
        "min_bad_final_combined_error": min((summary.final_combined_error for summary in bad), default=0.0),
        "min_bad_min_combined_error": min((summary.min_combined_error for summary in bad), default=0.0),
    }


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    validate_args(args)
    specs = profile_specs()
    grid = radial_grid(args.radius_max, args.samples)
    rows_by_profile: dict[str, list[DepthRow]] = {}
    for spec in specs:
        rows_by_profile[spec.name] = [compute_row(spec, depth, args, grid) for depth in range(args.depths)]

    summaries = [summarize_profile(spec, rows_by_profile[spec.name], args) for spec in specs]
    good_cases = [summary for summary in summaries if summary.expected_good]
    bad_cases = [summary for summary in summaries if not summary.expected_good]
    metrics = aggregate_metrics(summaries)
    validation_flags = {
        "all_profiles_classified_as_expected": all(summary.checks["expected_classification_met"] for summary in summaries),
        "all_good_cases_absorbed": metrics["good_cases_absorbed"] == metrics["good_case_count"],
        "all_bad_cases_rejected": metrics["bad_cases_rejected"] == metrics["bad_case_count"],
        "all_errors_finite_nonnegative": all(summary.checks["finite_nonnegative_errors"] for summary in summaries),
        "promotion_false": True,
        "diagnostic_only": True,
    }
    ok = all(validation_flags.values())
    return {
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": {
            "depths": args.depths,
            "radius_max": args.radius_max,
            "samples": args.samples,
            "base_cutoff_radius": args.base_cutoff_radius,
            "cutoff_step": args.cutoff_step,
            "transition_width": args.transition_width,
            "tolerance": args.tolerance,
            "good_decay_ratio": args.good_decay_ratio,
            "bad_floor": args.bad_floor,
            "pressure_weight": args.pressure_weight,
            "commutator_weight": args.commutator_weight,
            "gradient_weight": args.gradient_weight,
        },
        "good_cases": [asdict(summary) for summary in good_cases],
        "bad_cases": [asdict(summary) for summary in bad_cases],
        "aggregate_metrics": metrics,
        "validation_flags": validation_flags,
        "rows": {name: [asdict(row) for row in rows] for name, rows in rows_by_profile.items()},
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = build_payload(args)
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json:
        print(text)
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
