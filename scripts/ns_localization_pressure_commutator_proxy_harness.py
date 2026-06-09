#!/usr/bin/env python3
"""NS localization pressure/commutator proxy harness.

This pure-stdlib diagnostic simulates localized dyadic shell profiles for the
bookkeeping surface:

    local cutoff profile + pressure localization
    -> pressure tail error + cutoff/pressure commutator error
    -> refinement should drive both errors below tolerance for good profiles

Good profiles are compact or rapidly decaying outside the cutoff scale, so the
proxy errors decay as the refinement depth grows.  Bad profiles either retain a
large pressure tail or keep a large cutoff commutator.

This is a finite diagnostic only.  It does not prove a Navier-Stokes pressure
localization theorem, global regularity, or any Clay claim.  Promotion is
always false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


DEFAULT_OUTPUT = Path("outputs/ns_localization_pressure_commutator_proxy_harness.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class RefinementRow:
    profile: str
    refinement_depth: int
    shell_frequency: int
    cutoff_radius: float
    localization_width: float
    pressure_tail_error: float
    cutoff_commutator_error: float
    combined_error: float
    tolerance: float
    within_tolerance: bool


@dataclass(frozen=True)
class ProfileSummary:
    name: str
    description: str
    expected_good: bool
    rows: list[RefinementRow]
    initial_error: float
    final_error: float
    max_error: float
    min_error: float
    decay_ratio: float
    pressure_tail_final: float
    cutoff_commutator_final: float
    passed_expected_classification: bool
    classification: str
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refinements", type=int, default=9)
    parser.add_argument("--base-cutoff-radius", type=float, default=1.0)
    parser.add_argument("--localization-width", type=float, default=0.36)
    parser.add_argument("--tolerance", type=float, default=2.5e-3)
    parser.add_argument("--good-decay-factor", type=float, default=0.35)
    parser.add_argument("--bad-min-error", type=float, default=6.0e-2)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.refinements < 4:
        raise ValueError("--refinements must be at least 4")
    if args.base_cutoff_radius <= 0.0:
        raise ValueError("--base-cutoff-radius must be positive")
    if args.localization_width <= 0.0:
        raise ValueError("--localization-width must be positive")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if not (0.0 < args.good_decay_factor < 1.0):
        raise ValueError("--good-decay-factor must satisfy 0 < factor < 1")
    if args.bad_min_error <= args.tolerance:
        raise ValueError("--bad-min-error must be larger than --tolerance")


def profile_specs() -> list[tuple[str, str, bool, Callable[[int], tuple[float, float]]]]:
    return [
        (
            "good_compact_pressure_shell",
            "Localized shell with compact pressure support after cutoff refinement.",
            True,
            lambda depth: (
                0.40 * math.exp(-0.92 * depth),
                0.30 * math.exp(-0.84 * depth),
            ),
        ),
        (
            "good_schwartz_tail_shell",
            "Rapidly decaying pressure tail with a smooth cutoff transition.",
            True,
            lambda depth: (
                0.32 / ((depth + 2.0) ** 4.0),
                0.28 / ((depth + 2.0) ** 3.7),
            ),
        ),
        (
            "bad_pressure_tail_plateau",
            "Deliberately bad profile: pressure tail remains large under refinement.",
            False,
            lambda depth: (
                0.115 + 0.012 * math.sin(0.8 * depth),
                0.018 / math.sqrt(depth + 1.0),
            ),
        ),
        (
            "bad_cutoff_commutator_plateau",
            "Deliberately bad profile: cutoff commutator does not localize away.",
            False,
            lambda depth: (
                0.020 / ((depth + 1.0) ** 1.4),
                0.092 + 0.010 * math.cos(0.7 * depth),
            ),
        ),
    ]


def build_rows(
    *,
    name: str,
    refinements: int,
    base_cutoff_radius: float,
    localization_width: float,
    tolerance: float,
    error_fn: Callable[[int], tuple[float, float]],
) -> list[RefinementRow]:
    rows: list[RefinementRow] = []
    for depth in range(refinements):
        pressure_tail, cutoff_commutator = error_fn(depth)
        pressure_tail = max(0.0, pressure_tail)
        cutoff_commutator = max(0.0, cutoff_commutator)
        combined = max(pressure_tail, cutoff_commutator)
        shell_frequency = 1 << depth
        rows.append(
            RefinementRow(
                profile=name,
                refinement_depth=depth,
                shell_frequency=shell_frequency,
                cutoff_radius=base_cutoff_radius * (1.0 + depth / max(1.0, refinements - 1.0)),
                localization_width=localization_width / math.sqrt(shell_frequency),
                pressure_tail_error=pressure_tail,
                cutoff_commutator_error=cutoff_commutator,
                combined_error=combined,
                tolerance=tolerance,
                within_tolerance=combined <= tolerance,
            )
        )
    return rows


def nonincreasing_after_first(rows: Sequence[RefinementRow]) -> bool:
    errors = [row.combined_error for row in rows]
    return all(next_error <= prev_error + EPS for prev_error, next_error in zip(errors, errors[1:]))


def summarize_profile(
    *,
    name: str,
    description: str,
    expected_good: bool,
    rows: list[RefinementRow],
    tolerance: float,
    good_decay_factor: float,
    bad_min_error: float,
) -> ProfileSummary:
    if not rows:
        raise ValueError("profile must have refinement rows")
    initial = rows[0].combined_error
    final = rows[-1].combined_error
    max_error = max(row.combined_error for row in rows)
    min_error = min(row.combined_error for row in rows)
    decay_ratio = final / max(initial, EPS)
    finite_nonnegative = all(
        math.isfinite(row.pressure_tail_error)
        and math.isfinite(row.cutoff_commutator_error)
        and row.pressure_tail_error >= 0.0
        and row.cutoff_commutator_error >= 0.0
        for row in rows
    )
    good_decay_visible = final <= tolerance and decay_ratio <= good_decay_factor
    bad_obstruction_visible = min_error >= bad_min_error
    if expected_good and good_decay_visible:
        classification = "good_localized_shell_decay"
    elif (not expected_good) and bad_obstruction_visible:
        classification = "bad_localization_obstruction_visible"
    else:
        classification = "unexpected_or_borderline_profile"
    checks = {
        "finite_nonnegative_errors": finite_nonnegative,
        "refinement_rows_present": bool(rows),
        "good_final_error_within_tolerance": final <= tolerance if expected_good else True,
        "good_decay_ratio_visible": decay_ratio <= good_decay_factor if expected_good else True,
        "good_errors_monotone_after_refinement": nonincreasing_after_first(rows) if expected_good else True,
        "bad_min_error_above_threshold": min_error >= bad_min_error if not expected_good else True,
        "promotion_false": True,
    }
    return ProfileSummary(
        name=name,
        description=description,
        expected_good=expected_good,
        rows=rows,
        initial_error=initial,
        final_error=final,
        max_error=max_error,
        min_error=min_error,
        decay_ratio=decay_ratio,
        pressure_tail_final=rows[-1].pressure_tail_error,
        cutoff_commutator_final=rows[-1].cutoff_commutator_error,
        passed_expected_classification=classification
        in {"good_localized_shell_decay", "bad_localization_obstruction_visible"},
        classification=classification,
        checks=checks,
    )


def run(
    *,
    refinements: int,
    base_cutoff_radius: float,
    localization_width: float,
    tolerance: float,
    good_decay_factor: float,
    bad_min_error: float,
) -> dict[str, object]:
    profiles: list[ProfileSummary] = []
    for name, description, expected_good, error_fn in profile_specs():
        rows = build_rows(
            name=name,
            refinements=refinements,
            base_cutoff_radius=base_cutoff_radius,
            localization_width=localization_width,
            tolerance=tolerance,
            error_fn=error_fn,
        )
        profiles.append(
            summarize_profile(
                name=name,
                description=description,
                expected_good=expected_good,
                rows=rows,
                tolerance=tolerance,
                good_decay_factor=good_decay_factor,
                bad_min_error=bad_min_error,
            )
        )

    good_profiles = [profile for profile in profiles if profile.expected_good]
    bad_profiles = [profile for profile in profiles if not profile.expected_good]
    max_good_error = max(profile.final_error for profile in good_profiles)
    min_bad_error = min(profile.min_error for profile in bad_profiles)
    validation_flags = {
        "all_profiles_classified_as_expected": all(
            profile.passed_expected_classification for profile in profiles
        ),
        "good_profiles_decay_under_refinement": all(
            profile.final_error <= tolerance
            and profile.decay_ratio <= good_decay_factor
            and nonincreasing_after_first(profile.rows)
            for profile in good_profiles
        ),
        "bad_profiles_stay_large": all(profile.min_error >= bad_min_error for profile in bad_profiles),
        "max_good_error_within_tolerance": max_good_error <= tolerance,
        "min_bad_error_above_tolerance": min_bad_error > tolerance,
        "promotion_false": True,
        "finite_nonnegative_errors": all(
            profile.checks["finite_nonnegative_errors"] for profile in profiles
        ),
    }
    ok = all(validation_flags.values())
    return {
        "control": {
            "O": "Lane 4 Fermi finite NS localization pressure/commutator proxy.",
            "R": "Check that good localized shell profiles decay under refinement while bad pressure-tail or cutoff-commutator profiles remain obstructed.",
            "C": "scripts/ns_localization_pressure_commutator_proxy_harness.py",
            "S": "Pure stdlib finite profile simulation; no Agda, manifest, docs, or PDE theorem edits.",
            "L": "define profile error laws -> compute refinement rows -> classify good/bad behavior -> emit fail-closed JSON.",
            "P": "Use deterministic positive proxy errors for pressure tails and cutoff commutators across dyadic refinements.",
            "G": "promotion=false always; a passing proxy cannot certify Navier-Stokes regularity or Clay progress.",
            "F": "Does not construct true Leray pressure localization estimates or prove cutoff commutator bounds for PDE solutions.",
        },
        "ok": ok,
        "promotion": False,
        "parameters": {
            "refinements": refinements,
            "base_cutoff_radius": base_cutoff_radius,
            "localization_width": localization_width,
            "tolerance": tolerance,
            "good_decay_factor": good_decay_factor,
            "bad_min_error": bad_min_error,
        },
        "good_case_summaries": [
            asdict(profile) for profile in good_profiles
        ],
        "bad_case_summaries": [
            asdict(profile) for profile in bad_profiles
        ],
        "max_good_error": max_good_error,
        "min_bad_error": min_bad_error,
        "tolerance": tolerance,
        "validation_flags": validation_flags,
        "interpretation": {
            "supports": (
                "Finite proxy localized shell profiles can separate refinement-decaying pressure/cutoff errors from persistent obstructions."
            ),
            "rejects": (
                "Profiles with persistent pressure tails or cutoff commutators are not acceptable localization witnesses in this proxy."
            ),
            "residual_gap": (
                "A real proof still needs analytic pressure-tail estimates and cutoff commutator bounds for Navier-Stokes fields."
            ),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    summary = run(
        refinements=args.refinements,
        base_cutoff_radius=args.base_cutoff_radius,
        localization_width=args.localization_width,
        tolerance=args.tolerance,
        good_decay_factor=args.good_decay_factor,
        bad_min_error=args.bad_min_error,
    )
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("NS localization pressure/commutator proxy harness")
        print(f"ok={str(summary['ok']).lower()}")
        print("promotion=false")
        print(f"max_good_error={summary['max_good_error']:.6g}")
        print(f"min_bad_error={summary['min_bad_error']:.6g}")
        print(f"tolerance={summary['tolerance']:.6g}")
    return 0 if summary["ok"] and not summary["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
