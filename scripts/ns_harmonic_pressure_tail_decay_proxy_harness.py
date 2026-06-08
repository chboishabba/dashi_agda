#!/usr/bin/env python3
"""NS harmonic pressure-tail decay/absorption proxy harness.

This pure-stdlib diagnostic models a finite harmonic pressure-tail bookkeeping
surface.  It checks that source neutrality, annular separation, and high moment
cancellation drive a synthetic exterior harmonic tail below tolerance, while
deliberately bad profiles keep visible obstructions.

The harness is diagnostic only: it does not solve Navier-Stokes, construct a
pressure representation theorem, or promote any Clay/unification claim.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


DEFAULT_OUTPUT = Path("outputs/ns_harmonic_pressure_tail_decay_proxy_harness.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class CaseSpec:
    name: str
    family: str
    description: str
    expected_good: bool
    row_builder: Callable[[int, argparse.Namespace], "TailRow"]


@dataclass(frozen=True)
class TailRow:
    case: str
    family: str
    depth: int
    exterior_distance: float
    annular_separation: float
    moment_order: int
    mean_residual: float
    harmonic_tail_error: float
    absorption_error: float
    plateau_error: float
    combined_error: float
    tolerance: float
    within_tolerance: bool


@dataclass(frozen=True)
class CaseSummary:
    name: str
    family: str
    description: str
    expected_good: bool
    classification: str
    observed_pass: bool
    row_count: int
    initial_combined_error: float
    final_combined_error: float
    decay_ratio: float
    min_combined_error: float
    max_combined_error: float
    final_moment_order: int
    final_mean_residual: float
    final_harmonic_tail_error: float
    final_absorption_error: float
    final_plateau_error: float
    rows_within_tolerance: int
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", type=int, default=10, help="Number of deterministic refinement depths.")
    parser.add_argument("--tolerance", type=float, default=3.0e-3)
    parser.add_argument("--good-decay-ratio", type=float, default=0.12)
    parser.add_argument("--bad-floor", type=float, default=2.0e-2)
    parser.add_argument("--tail-radius", type=float, default=1.0)
    parser.add_argument("--base-exterior-distance", type=float, default=4.8)
    parser.add_argument("--distance-step", type=float, default=0.75)
    parser.add_argument("--base-annular-separation", type=float, default=2.6)
    parser.add_argument("--separation-step", type=float, default=0.72)
    parser.add_argument("--moment-growth", type=int, default=2)
    parser.add_argument("--source-amplitude", type=float, default=0.34)
    parser.add_argument("--absorption-weight", type=float, default=0.55)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.depths < 5:
        raise ValueError("--depths must be at least 5")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if not (0.0 < args.good_decay_ratio < 1.0):
        raise ValueError("--good-decay-ratio must satisfy 0 < ratio < 1")
    if args.bad_floor <= args.tolerance:
        raise ValueError("--bad-floor must be larger than --tolerance")
    if args.tail_radius <= 0.0:
        raise ValueError("--tail-radius must be positive")
    if args.base_exterior_distance <= args.tail_radius:
        raise ValueError("--base-exterior-distance must exceed --tail-radius")
    if args.distance_step <= 0.0:
        raise ValueError("--distance-step must be positive")
    if args.base_annular_separation <= 0.0:
        raise ValueError("--base-annular-separation must be positive")
    if args.separation_step <= 0.0:
        raise ValueError("--separation-step must be positive")
    if args.moment_growth < 1:
        raise ValueError("--moment-growth must be at least 1")
    if args.source_amplitude <= 0.0:
        raise ValueError("--source-amplitude must be positive")
    if args.absorption_weight <= 0.0:
        raise ValueError("--absorption-weight must be positive")


def harmonic_tail(amplitude: float, radius: float, distance: float, moment_order: int) -> float:
    ratio = radius / max(distance, radius + EPS)
    return amplitude * (ratio ** (moment_order + 1))


def make_row(
    *,
    case: str,
    family: str,
    depth: int,
    exterior_distance: float,
    annular_separation: float,
    moment_order: int,
    mean_residual: float,
    harmonic_tail_error: float,
    absorption_error: float,
    plateau_error: float,
    tolerance: float,
) -> TailRow:
    combined = max(mean_residual, harmonic_tail_error, absorption_error, plateau_error)
    return TailRow(
        case=case,
        family=family,
        depth=depth,
        exterior_distance=exterior_distance,
        annular_separation=annular_separation,
        moment_order=moment_order,
        mean_residual=mean_residual,
        harmonic_tail_error=harmonic_tail_error,
        absorption_error=absorption_error,
        plateau_error=plateau_error,
        combined_error=combined,
        tolerance=tolerance,
        within_tolerance=combined <= tolerance,
    )


def mean_subtracted_exterior_source(depth: int, args: argparse.Namespace) -> TailRow:
    distance = args.base_exterior_distance + args.distance_step * depth
    moment = 1 + depth // 2
    tail = harmonic_tail(args.source_amplitude, args.tail_radius, distance, moment)
    absorption = args.absorption_weight * tail / (1.0 + 0.35 * depth)
    return make_row(
        case="good_mean_subtracted_exterior_source",
        family="mean_subtracted_exterior_source",
        depth=depth,
        exterior_distance=distance,
        annular_separation=distance - args.tail_radius,
        moment_order=moment,
        mean_residual=0.0,
        harmonic_tail_error=tail,
        absorption_error=absorption,
        plateau_error=0.0,
        tolerance=args.tolerance,
    )


def separated_annular_tail(depth: int, args: argparse.Namespace) -> TailRow:
    separation = args.base_annular_separation + args.separation_step * depth
    distance = args.tail_radius + separation
    tail = 0.22 / ((1.0 + separation) ** 3.2)
    absorption = 0.12 / ((1.0 + separation) ** 3.6)
    return make_row(
        case="good_separated_annular_tail",
        family="separated_annular_tail",
        depth=depth,
        exterior_distance=distance,
        annular_separation=separation,
        moment_order=2,
        mean_residual=0.0,
        harmonic_tail_error=tail,
        absorption_error=absorption,
        plateau_error=0.0,
        tolerance=args.tolerance,
    )


def high_moment_harmonic_tail(depth: int, args: argparse.Namespace) -> TailRow:
    distance = args.base_exterior_distance
    moment = 1 + args.moment_growth * depth
    tail = harmonic_tail(0.52 * args.source_amplitude, args.tail_radius, distance, moment)
    absorption = args.absorption_weight * tail / math.sqrt(1.0 + depth)
    return make_row(
        case="good_high_moment_harmonic_tail_decay",
        family="high_moment_harmonic_tail_decay",
        depth=depth,
        exterior_distance=distance,
        annular_separation=distance - args.tail_radius,
        moment_order=moment,
        mean_residual=0.0,
        harmonic_tail_error=tail,
        absorption_error=absorption,
        plateau_error=0.0,
        tolerance=args.tolerance,
    )


def non_mean_subtracted_monopole(depth: int, args: argparse.Namespace) -> TailRow:
    distance = args.base_exterior_distance + 0.25 * args.distance_step * depth
    mean_residual = 0.052 + 0.004 * math.cos(0.7 * depth)
    tail = mean_residual + harmonic_tail(0.18, args.tail_radius, distance, 0)
    return make_row(
        case="bad_non_mean_subtracted_monopole",
        family="non_mean_subtracted_monopole",
        depth=depth,
        exterior_distance=distance,
        annular_separation=distance - args.tail_radius,
        moment_order=0,
        mean_residual=mean_residual,
        harmonic_tail_error=tail,
        absorption_error=0.45 * tail,
        plateau_error=0.0,
        tolerance=args.tolerance,
    )


def nearby_exterior_source(depth: int, args: argparse.Namespace) -> TailRow:
    distance = args.tail_radius + 0.34 + 0.025 * math.sin(float(depth))
    tail = harmonic_tail(0.10, args.tail_radius, distance, 1)
    absorption = 0.024 + 0.006 / (1.0 + depth)
    return make_row(
        case="bad_nearby_exterior_source",
        family="nearby_exterior_source",
        depth=depth,
        exterior_distance=distance,
        annular_separation=distance - args.tail_radius,
        moment_order=1,
        mean_residual=0.0,
        harmonic_tail_error=tail,
        absorption_error=absorption,
        plateau_error=0.0,
        tolerance=args.tolerance,
    )


def persistent_harmonic_plateau(depth: int, args: argparse.Namespace) -> TailRow:
    distance = args.base_exterior_distance + args.distance_step * depth
    plateau = 0.033 + 0.003 * math.sin(0.9 * depth)
    tail = harmonic_tail(0.08, args.tail_radius, distance, 4)
    return make_row(
        case="bad_persistent_harmonic_plateau",
        family="persistent_harmonic_plateau",
        depth=depth,
        exterior_distance=distance,
        annular_separation=distance - args.tail_radius,
        moment_order=4 + depth,
        mean_residual=0.0,
        harmonic_tail_error=tail,
        absorption_error=0.35 * plateau,
        plateau_error=plateau,
        tolerance=args.tolerance,
    )


def case_specs() -> list[CaseSpec]:
    return [
        CaseSpec(
            name="good_mean_subtracted_exterior_source",
            family="mean_subtracted_exterior_source",
            description="Exterior source with monopole removed; harmonic tail decays under separation.",
            expected_good=True,
            row_builder=mean_subtracted_exterior_source,
        ),
        CaseSpec(
            name="good_separated_annular_tail",
            family="separated_annular_tail",
            description="Annular pressure tail separated from the localization region and absorbed by decay.",
            expected_good=True,
            row_builder=separated_annular_tail,
        ),
        CaseSpec(
            name="good_high_moment_harmonic_tail_decay",
            family="high_moment_harmonic_tail_decay",
            description="High-order moment cancellation forces harmonic pressure-tail decay below tolerance.",
            expected_good=True,
            row_builder=high_moment_harmonic_tail,
        ),
        CaseSpec(
            name="bad_non_mean_subtracted_monopole",
            family="non_mean_subtracted_monopole",
            description="Monopole is not mean-subtracted, leaving a persistent pressure-tail obstruction.",
            expected_good=False,
            row_builder=non_mean_subtracted_monopole,
        ),
        CaseSpec(
            name="bad_nearby_exterior_source",
            family="nearby_exterior_source",
            description="Exterior source is too close to be absorbed by the annular tail estimate.",
            expected_good=False,
            row_builder=nearby_exterior_source,
        ),
        CaseSpec(
            name="bad_persistent_harmonic_plateau",
            family="persistent_harmonic_plateau",
            description="Harmonic plateau remains above tolerance despite moment refinement.",
            expected_good=False,
            row_builder=persistent_harmonic_plateau,
        ),
    ]


def nonincreasing(values: Sequence[float], slack: float = 1.0e-10) -> bool:
    return all(nxt <= prev + slack for prev, nxt in zip(values, values[1:]))


def summarize_case(spec: CaseSpec, rows: Sequence[TailRow], args: argparse.Namespace) -> CaseSummary:
    if not rows:
        raise ValueError(f"case {spec.name} produced no rows")

    initial = rows[0].combined_error
    final = rows[-1].combined_error
    decay_ratio = final / max(initial, EPS)
    min_error = min(row.combined_error for row in rows)
    max_error = max(row.combined_error for row in rows)
    rows_within = sum(1 for row in rows if row.within_tolerance)
    finite_nonnegative = all(
        math.isfinite(row.combined_error)
        and row.mean_residual >= 0.0
        and row.harmonic_tail_error >= 0.0
        and row.absorption_error >= 0.0
        and row.plateau_error >= 0.0
        for row in rows
    )

    good_pass = (
        final <= args.tolerance
        and decay_ratio <= args.good_decay_ratio
        and rows[-1].mean_residual <= EPS
    )
    bad_fails = final >= args.bad_floor or min_error >= args.bad_floor
    observed_pass = good_pass if spec.expected_good else not bad_fails

    if spec.expected_good and good_pass:
        classification = "good_harmonic_tail_absorbed_below_tolerance"
    elif (not spec.expected_good) and bad_fails:
        classification = "bad_harmonic_tail_obstruction_detected"
    else:
        classification = "unexpected_or_borderline"

    checks = {
        "finite_nonnegative_errors": finite_nonnegative,
        "rows_present": len(rows) == args.depths,
        "final_error_below_tolerance_for_good": final <= args.tolerance if spec.expected_good else True,
        "decay_ratio_below_good_threshold": decay_ratio <= args.good_decay_ratio if spec.expected_good else True,
        "mean_residual_zero_for_good": rows[-1].mean_residual <= EPS if spec.expected_good else True,
        "bad_obstruction_above_floor": bad_fails if not spec.expected_good else True,
        "good_tail_nonincreasing": nonincreasing([row.combined_error for row in rows])
        if spec.expected_good
        else True,
        "expected_classification_met": (spec.expected_good and good_pass) or ((not spec.expected_good) and bad_fails),
        "promotion_false": True,
        "diagnostic_only": True,
    }
    return CaseSummary(
        name=spec.name,
        family=spec.family,
        description=spec.description,
        expected_good=spec.expected_good,
        classification=classification,
        observed_pass=observed_pass,
        row_count=len(rows),
        initial_combined_error=initial,
        final_combined_error=final,
        decay_ratio=decay_ratio,
        min_combined_error=min_error,
        max_combined_error=max_error,
        final_moment_order=rows[-1].moment_order,
        final_mean_residual=rows[-1].mean_residual,
        final_harmonic_tail_error=rows[-1].harmonic_tail_error,
        final_absorption_error=rows[-1].absorption_error,
        final_plateau_error=rows[-1].plateau_error,
        rows_within_tolerance=rows_within,
        checks=checks,
    )


def aggregate_metrics(summaries: Sequence[CaseSummary]) -> dict[str, float | int]:
    good = [summary for summary in summaries if summary.expected_good]
    bad = [summary for summary in summaries if not summary.expected_good]
    return {
        "good_case_count": len(good),
        "bad_case_count": len(bad),
        "good_cases_absorbed": sum(
            1 for summary in good if summary.classification == "good_harmonic_tail_absorbed_below_tolerance"
        ),
        "bad_cases_rejected": sum(
            1 for summary in bad if summary.classification == "bad_harmonic_tail_obstruction_detected"
        ),
        "max_good_final_combined_error": max((summary.final_combined_error for summary in good), default=0.0),
        "max_good_decay_ratio": max((summary.decay_ratio for summary in good), default=0.0),
        "min_bad_final_combined_error": min((summary.final_combined_error for summary in bad), default=0.0),
        "min_bad_min_combined_error": min((summary.min_combined_error for summary in bad), default=0.0),
        "max_final_moment_order": max((summary.final_moment_order for summary in summaries), default=0),
    }


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    validate_args(args)
    specs = case_specs()
    rows_by_case = {
        spec.name: [spec.row_builder(depth, args) for depth in range(args.depths)] for spec in specs
    }
    summaries = [summarize_case(spec, rows_by_case[spec.name], args) for spec in specs]
    good_cases = [summary for summary in summaries if summary.expected_good]
    bad_cases = [summary for summary in summaries if not summary.expected_good]
    metrics = aggregate_metrics(summaries)
    validation_flags = {
        "all_cases_classified_as_expected": all(summary.checks["expected_classification_met"] for summary in summaries),
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
        "harness": "ns_harmonic_pressure_tail_decay_proxy",
        "control": {
            "O": "NS harmonic pressure-tail decay/absorption proxy diagnostic.",
            "R": "Check source neutrality, annular separation, and moment cancellation against fail-closed bad cases.",
            "C": "scripts/ns_harmonic_pressure_tail_decay_proxy_harness.py",
            "S": "Finite deterministic synthetic model; no PDE pressure theorem is constructed.",
            "L": "source moments -> harmonic tail estimate -> annular absorption proxy -> classification flags",
            "P": "Good cases must decay below tolerance; bad cases must retain visible obstruction.",
            "G": "promotion=false and diagnostic_only=true regardless of outcome.",
            "F": "Does not prove Navier-Stokes regularity, pressure localization, or any Clay claim.",
        },
        "parameters": {
            "depths": args.depths,
            "tolerance": args.tolerance,
            "good_decay_ratio": args.good_decay_ratio,
            "bad_floor": args.bad_floor,
            "tail_radius": args.tail_radius,
            "base_exterior_distance": args.base_exterior_distance,
            "distance_step": args.distance_step,
            "base_annular_separation": args.base_annular_separation,
            "separation_step": args.separation_step,
            "moment_growth": args.moment_growth,
            "source_amplitude": args.source_amplitude,
            "absorption_weight": args.absorption_weight,
        },
        "good_cases": [asdict(summary) for summary in good_cases],
        "bad_cases": [asdict(summary) for summary in bad_cases],
        "aggregate_metrics": metrics,
        "validation_flags": validation_flags,
        "rows": {name: [asdict(row) for row in rows] for name, rows in rows_by_case.items()},
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
