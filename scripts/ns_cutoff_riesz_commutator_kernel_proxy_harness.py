#!/usr/bin/env python3
"""A6 cutoff/Riesz commutator kernel proxy harness.

This pure-stdlib diagnostic models a finite estimate for

    [P_j, phi] R_i R_l

on radial dyadic shells.  It tracks the scale 2^-j, cutoff transition
smoothness, annulus separation, signed kernel cancellation/moment gain, and an
epsilon-gradient absorption budget.  Good profiles are expected to fall below
tolerance; deliberately bad profiles are expected to fail.

The calculations are deterministic finite quadratures and estimate proxies
only.  They prove no Navier-Stokes theorem and never promote a result:
promotion=false and diagnostic_only=true are invariant output fields.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ns_cutoff_riesz_commutator_kernel_proxy_harness.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class CaseSpec:
    name: str
    kind: str
    description: str
    expected_good: bool
    cutoff_smoothness: int
    cancellation_order: int
    annulus_inner: float
    annulus_outer: float
    shell_center_factor: float
    shell_width_factor: float
    amplitude: float
    recentered: bool
    roughness_multiplier: float
    epsilon_gradient: float
    gradient_margin: float


@dataclass(frozen=True)
class DiagnosticRow:
    case: str
    kind: str
    j: int
    dyadic_scale: float
    cutoff_transition_width: float
    annulus_separation: float
    cutoff_gradient_norm: float
    kernel_l1_radius: float
    signed_kernel_moment: float
    cancellation_gain: float
    raw_commutator_error: float
    moment_corrected_error: float
    epsilon_absorbed_gradient: float
    nonabsorbed_gradient_error: float
    combined_error: float
    tolerance: float
    within_tolerance: bool


@dataclass(frozen=True)
class CaseSummary:
    name: str
    kind: str
    description: str
    expected_good: bool
    observed_pass: bool
    classification: str
    row_count: int
    initial_error: float
    final_error: float
    decay_ratio: float
    max_error: float
    min_error: float
    min_annulus_separation: float
    final_cancellation_gain: float
    final_nonabsorbed_gradient_error: float
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-j", type=int, default=4, help="Smallest dyadic scale index.")
    parser.add_argument("--max-j", type=int, default=10, help="Largest dyadic scale index.")
    parser.add_argument("--samples", type=int, default=900, help="Radial quadrature samples.")
    parser.add_argument("--radius-max", type=float, default=5.0, help="Maximum kernel radius.")
    parser.add_argument("--base-transition-width", type=float, default=0.32)
    parser.add_argument("--core-radius", type=float, default=1.0)
    parser.add_argument("--tolerance", type=float, default=1.8e-3)
    parser.add_argument("--good-decay-ratio", type=float, default=0.22)
    parser.add_argument("--bad-floor", type=float, default=5.0e-3)
    parser.add_argument("--kernel-tail-power", type=float, default=3.0)
    parser.add_argument("--moment-strength", type=float, default=0.85)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.min_j < 1:
        raise ValueError("--min-j must be positive")
    if args.max_j < args.min_j + 3:
        raise ValueError("--max-j must be at least min-j + 3")
    if args.samples < 200:
        raise ValueError("--samples must be at least 200")
    if args.radius_max <= 1.0:
        raise ValueError("--radius-max must exceed 1")
    if args.base_transition_width <= 0.0:
        raise ValueError("--base-transition-width must be positive")
    if args.core_radius <= 0.0:
        raise ValueError("--core-radius must be positive")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if not (0.0 < args.good_decay_ratio < 1.0):
        raise ValueError("--good-decay-ratio must satisfy 0 < ratio < 1")
    if args.bad_floor <= args.tolerance:
        raise ValueError("--bad-floor must exceed --tolerance")
    if args.kernel_tail_power <= 1.0:
        raise ValueError("--kernel-tail-power must exceed 1")
    if not (0.0 < args.moment_strength <= 1.0):
        raise ValueError("--moment-strength must satisfy 0 < strength <= 1")


def case_specs() -> list[CaseSpec]:
    return [
        CaseSpec(
            name="good_smooth_compact_cutoff_moment_cancelled",
            kind="smooth_compact_cutoff",
            description="Smooth compact cutoff, separated source shell, second moment cancellation.",
            expected_good=True,
            cutoff_smoothness=4,
            cancellation_order=2,
            annulus_inner=1.72,
            annulus_outer=2.42,
            shell_center_factor=1.04,
            shell_width_factor=0.24,
            amplitude=0.20,
            recentered=False,
            roughness_multiplier=1.0,
            epsilon_gradient=0.88,
            gradient_margin=1.15,
        ),
        CaseSpec(
            name="good_separated_annulus_high_moment",
            kind="separated_annulus",
            description="Annulus is far from the cutoff core and has third-order kernel moment gain.",
            expected_good=True,
            cutoff_smoothness=5,
            cancellation_order=3,
            annulus_inner=2.10,
            annulus_outer=2.95,
            shell_center_factor=1.00,
            shell_width_factor=0.20,
            amplitude=0.24,
            recentered=False,
            roughness_multiplier=0.92,
            epsilon_gradient=0.92,
            gradient_margin=1.25,
        ),
        CaseSpec(
            name="good_shell_recentered_profile",
            kind="shell_recentered_profile",
            description="Profile is recentered around the shell midpoint before applying cancellation.",
            expected_good=True,
            cutoff_smoothness=4,
            cancellation_order=3,
            annulus_inner=1.58,
            annulus_outer=2.10,
            shell_center_factor=1.00,
            shell_width_factor=0.16,
            amplitude=0.18,
            recentered=True,
            roughness_multiplier=0.82,
            epsilon_gradient=0.90,
            gradient_margin=1.20,
        ),
        CaseSpec(
            name="bad_rough_cutoff",
            kind="rough_cutoff",
            description="Only Lipschitz-scale cutoff smoothness, leaving a large commutator gradient.",
            expected_good=False,
            cutoff_smoothness=0,
            cancellation_order=2,
            annulus_inner=1.72,
            annulus_outer=2.42,
            shell_center_factor=1.04,
            shell_width_factor=0.24,
            amplitude=0.46,
            recentered=False,
            roughness_multiplier=7.0,
            epsilon_gradient=0.28,
            gradient_margin=0.72,
        ),
        CaseSpec(
            name="bad_no_cancellation",
            kind="no_cancellation",
            description="Separated shell without moment cancellation in the Riesz kernel proxy.",
            expected_good=False,
            cutoff_smoothness=4,
            cancellation_order=0,
            annulus_inner=1.92,
            annulus_outer=2.72,
            shell_center_factor=1.00,
            shell_width_factor=0.22,
            amplitude=0.52,
            recentered=False,
            roughness_multiplier=1.0,
            epsilon_gradient=0.82,
            gradient_margin=1.05,
        ),
        CaseSpec(
            name="bad_annulus_touching_core",
            kind="annulus_touching_core",
            description="The annulus touches the cutoff core, so separation gain is absent.",
            expected_good=False,
            cutoff_smoothness=4,
            cancellation_order=2,
            annulus_inner=1.02,
            annulus_outer=1.34,
            shell_center_factor=0.92,
            shell_width_factor=0.22,
            amplitude=0.50,
            recentered=False,
            roughness_multiplier=1.15,
            epsilon_gradient=0.55,
            gradient_margin=0.70,
        ),
    ]


def radial_grid(radius_max: float, samples: int) -> list[tuple[float, float]]:
    dr = radius_max / samples
    return [((index + 0.5) * dr, dr) for index in range(samples)]


def gaussian(x: float, center: float, width: float) -> float:
    z = (x - center) / max(width, EPS)
    return math.exp(-0.5 * z * z)


def kernel_abs_density(radius: float, dyadic_scale: float, tail_power: float) -> float:
    rho = radius / max(dyadic_scale, EPS)
    bandpass = (1.0 + rho + 0.35 * rho * rho) * math.exp(-0.5 * rho * rho)
    riesz_tail = 1.0 / ((1.0 + radius) ** tail_power)
    return bandpass * riesz_tail / max(dyadic_scale, EPS) ** 3


def signed_kernel_density(radius: float, dyadic_scale: float, tail_power: float) -> float:
    rho = radius / max(dyadic_scale, EPS)
    mexican_hat = (1.0 - rho * rho / 3.0) * math.exp(-0.5 * rho * rho)
    riesz_tail = 1.0 / ((1.0 + radius) ** tail_power)
    return mexican_hat * riesz_tail / max(dyadic_scale, EPS) ** 3


def cutoff_transition_width(base: float, smoothness: int, j: int, min_j: int) -> float:
    if smoothness <= 0:
        return base * 0.25
    refinement = 1.0 + 0.10 * smoothness * (j - min_j)
    return base * refinement


def cutoff_difference_bound(radius: float, width: float, smoothness: int, roughness: float) -> float:
    gradient = roughness / max(width, EPS)
    holder_gain = min(1.0, (radius / max(width, EPS)) ** max(1, smoothness + 1))
    if smoothness <= 0:
        holder_gain = 1.0
    return min(2.0, gradient * radius * holder_gain)


def shell_profile(radius: float, spec: CaseSpec) -> float:
    center = 0.5 * (spec.annulus_inner + spec.annulus_outer) * spec.shell_center_factor
    width = max(EPS, spec.shell_width_factor * (spec.annulus_outer - spec.annulus_inner))
    profile = spec.amplitude * gaussian(radius, center, width)
    if spec.recentered:
        recenter_gain = abs(radius - center) / max(width, EPS)
        profile *= min(1.0, 0.34 + 0.38 * recenter_gain)
    return profile


def integrate_row(
    spec: CaseSpec,
    *,
    j: int,
    min_j: int,
    grid: Sequence[tuple[float, float]],
    args: argparse.Namespace,
) -> DiagnosticRow:
    dyadic_scale = 2.0 ** (-j)
    width = cutoff_transition_width(args.base_transition_width, spec.cutoff_smoothness, j, min_j)
    separation = max(0.0, spec.annulus_inner - args.core_radius)
    cutoff_grad = spec.roughness_multiplier / max(width, EPS)

    raw = 0.0
    kernel_l1_radius = 0.0
    signed_moment = 0.0
    for radius, dr in grid:
        volume_weight = 4.0 * math.pi * radius * radius * dr
        abs_density = kernel_abs_density(radius, dyadic_scale, args.kernel_tail_power)
        signed_density = signed_kernel_density(radius, dyadic_scale, args.kernel_tail_power)
        phi_delta = cutoff_difference_bound(
            radius, width, spec.cutoff_smoothness, spec.roughness_multiplier
        )
        profile = shell_profile(radius + args.core_radius, spec)
        raw += abs_density * phi_delta * profile * volume_weight
        kernel_l1_radius += abs_density * radius * volume_weight
        signed_moment += signed_density * (radius**max(1, spec.cancellation_order)) * volume_weight

    separation_ratio = dyadic_scale / max(separation, dyadic_scale)
    if spec.cancellation_order <= 0:
        cancellation_gain = 1.0
        moment_factor = 1.0
    else:
        cancellation_gain = args.moment_strength * separation_ratio**spec.cancellation_order
        normalized_moment = abs(signed_moment) / max(kernel_l1_radius, EPS)
        moment_factor = min(1.0, cancellation_gain + normalized_moment)

    touching_penalty = 1.0 + max(0.0, args.core_radius + 0.18 - spec.annulus_inner) * 18.0
    moment_corrected = raw * moment_factor * touching_penalty
    if spec.cancellation_order <= 0:
        uncancelled_low_mode = 0.025 * spec.amplitude / math.sqrt(j)
        moment_corrected += uncancelled_low_mode

    scale_gradient_need = 0.00062 * cutoff_grad * spec.amplitude / math.sqrt(max(j, 1))
    absorbed = spec.epsilon_gradient * args.tolerance * spec.gradient_margin
    nonabsorbed = max(0.0, scale_gradient_need - absorbed)
    combined = moment_corrected + nonabsorbed

    return DiagnosticRow(
        case=spec.name,
        kind=spec.kind,
        j=j,
        dyadic_scale=dyadic_scale,
        cutoff_transition_width=width,
        annulus_separation=separation,
        cutoff_gradient_norm=cutoff_grad,
        kernel_l1_radius=kernel_l1_radius,
        signed_kernel_moment=signed_moment,
        cancellation_gain=cancellation_gain,
        raw_commutator_error=raw,
        moment_corrected_error=moment_corrected,
        epsilon_absorbed_gradient=absorbed,
        nonabsorbed_gradient_error=nonabsorbed,
        combined_error=combined,
        tolerance=args.tolerance,
        within_tolerance=combined <= args.tolerance,
    )


def summarize_case(
    spec: CaseSpec,
    rows: Sequence[DiagnosticRow],
    *,
    tolerance: float,
    good_decay_ratio: float,
    bad_floor: float,
) -> CaseSummary:
    if not rows:
        raise ValueError("case summary requires rows")
    initial = rows[0].combined_error
    final = rows[-1].combined_error
    max_error = max(row.combined_error for row in rows)
    min_error = min(row.combined_error for row in rows)
    decay_ratio = final / max(initial, EPS)
    observed_pass = all(row.within_tolerance for row in rows)
    bad_visible = (not observed_pass) and max_error >= bad_floor
    if spec.expected_good and observed_pass and decay_ratio <= good_decay_ratio:
        classification = "good_commutator_kernel_estimate_below_tolerance"
    elif (not spec.expected_good) and bad_visible:
        classification = "bad_commutator_obstruction_visible"
    else:
        classification = "unexpected_or_borderline_case"
    checks = {
        "finite_nonnegative_errors": all(
            math.isfinite(row.combined_error)
            and row.combined_error >= 0.0
            and row.raw_commutator_error >= 0.0
            and row.moment_corrected_error >= 0.0
            and row.nonabsorbed_gradient_error >= 0.0
            for row in rows
        ),
        "expected_outcome_observed": observed_pass == spec.expected_good,
        "good_final_below_tolerance": final <= tolerance if spec.expected_good else True,
        "good_decay_ratio_visible": decay_ratio <= good_decay_ratio if spec.expected_good else True,
        "bad_obstruction_above_floor_or_tolerance": bad_visible if not spec.expected_good else True,
        "annulus_separation_positive_for_good": min(row.annulus_separation for row in rows) > 0.0
        if spec.expected_good
        else True,
        "promotion_false": True,
        "diagnostic_only_true": True,
    }
    return CaseSummary(
        name=spec.name,
        kind=spec.kind,
        description=spec.description,
        expected_good=spec.expected_good,
        observed_pass=observed_pass,
        classification=classification,
        row_count=len(rows),
        initial_error=initial,
        final_error=final,
        decay_ratio=decay_ratio,
        max_error=max_error,
        min_error=min_error,
        min_annulus_separation=min(row.annulus_separation for row in rows),
        final_cancellation_gain=rows[-1].cancellation_gain,
        final_nonabsorbed_gradient_error=rows[-1].nonabsorbed_gradient_error,
        checks=checks,
    )


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    validate_args(args)
    grid = radial_grid(args.radius_max, args.samples)
    specs = case_specs()
    rows: list[DiagnosticRow] = []
    summaries: list[CaseSummary] = []
    for spec in specs:
        case_rows = [
            integrate_row(spec, j=j, min_j=args.min_j, grid=grid, args=args)
            for j in range(args.min_j, args.max_j + 1)
        ]
        rows.extend(case_rows)
        summaries.append(
            summarize_case(
                spec,
                case_rows,
                tolerance=args.tolerance,
                good_decay_ratio=args.good_decay_ratio,
                bad_floor=args.bad_floor,
            )
        )

    good_cases = [summary for summary in summaries if summary.expected_good]
    bad_cases = [summary for summary in summaries if not summary.expected_good]
    all_checks = [flag for summary in summaries for flag in summary.checks.values()]
    validation_flags = {
        "all_case_checks_pass": all(all_checks),
        "all_good_cases_pass": all(summary.observed_pass for summary in good_cases),
        "all_bad_cases_fail": all(not summary.observed_pass for summary in bad_cases),
        "promotion_false": True,
        "diagnostic_only_true": True,
        "deterministic_stdlib_only": True,
        "row_count_matches_grid": len(rows) == len(specs) * (args.max_j - args.min_j + 1),
    }
    aggregate_metrics = {
        "case_count": len(specs),
        "good_case_count": len(good_cases),
        "bad_case_count": len(bad_cases),
        "row_count": len(rows),
        "max_good_final_error": max(summary.final_error for summary in good_cases),
        "min_bad_final_error": min(summary.final_error for summary in bad_cases),
        "max_good_decay_ratio": max(summary.decay_ratio for summary in good_cases),
        "min_annulus_separation": min(row.annulus_separation for row in rows),
        "max_raw_commutator_error": max(row.raw_commutator_error for row in rows),
        "max_nonabsorbed_gradient_error": max(row.nonabsorbed_gradient_error for row in rows),
    }
    ok = all(validation_flags.values())
    return {
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": {
            "min_j": args.min_j,
            "max_j": args.max_j,
            "samples": args.samples,
            "radius_max": args.radius_max,
            "base_transition_width": args.base_transition_width,
            "core_radius": args.core_radius,
            "tolerance": args.tolerance,
            "good_decay_ratio": args.good_decay_ratio,
            "bad_floor": args.bad_floor,
            "kernel_tail_power": args.kernel_tail_power,
            "moment_strength": args.moment_strength,
        },
        "good_cases": [asdict(summary) for summary in good_cases],
        "bad_cases": [asdict(summary) for summary in bad_cases],
        "aggregate_metrics": aggregate_metrics,
        "validation_flags": validation_flags,
        "rows": [asdict(row) for row in rows],
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
