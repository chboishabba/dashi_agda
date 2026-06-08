#!/usr/bin/env python3
"""NS pointwise-to-Abel averaging proxy harness.

This pure-stdlib diagnostic exercises the A6 bookkeeping target:

    localized pointwise stretching  omega . S omega
    -> shell diagonal mean           lambda * (2 kappa^2 - 1)
    -> Abel/log-window average       small LLN-like residual

It simulates dyadic shell rows with diagonal stretching contributions,
off-diagonal noise, and Abel window averages.  LLN-like profiles are
constructed from arcsine-neutral kappa samples and centered off-diagonal terms.
A deliberately bad profile correlates kappa^2 with lambda and adds positive
off-diagonal drift, so the averaging error remains visible.

This is a diagnostic harness only.  It does not prove a PDE Abel LLN, a
compensated leakage identity, NS regularity, YM, or unification.  Promotion is
always false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


DEFAULT_OUTPUT = Path("outputs/ns_pointwise_to_abel_averaging_proxy_harness.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class ShellRow:
    profile: str
    shell_depth: int
    shell_frequency: int
    samples: int
    lambda_value: float
    diagonal_mean: float
    offdiag_mean: float
    pointwise_proxy_mean: float
    diagonal_abs_mean: float
    offdiag_abs_mean: float
    shell_lln_scale: float


@dataclass(frozen=True)
class AbelWindowRow:
    profile: str
    center_depth: int
    start_depth: int
    stop_depth: int
    window_width: int
    abel_diagonal_mean: float
    abel_offdiag_mean: float
    abel_pointwise_mean: float
    abel_abs_diagonal_mean: float
    abel_abs_offdiag_mean: float
    lln_tolerance: float
    within_lln_tolerance: bool


@dataclass(frozen=True)
class ProfileSummary:
    name: str
    description: str
    expected_lln_good: bool
    shell_rows: list[ShellRow]
    window_rows: list[AbelWindowRow]
    max_abs_abel_pointwise_mean: float
    mean_abs_abel_pointwise_mean: float
    max_abs_abel_diagonal_mean: float
    max_abs_abel_offdiag_mean: float
    lln_tolerance: float
    windows_within_tolerance_fraction: float
    classification: str
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shells", type=int, default=22, help="Number of dyadic shell depths.")
    parser.add_argument(
        "--samples-per-shell",
        type=int,
        default=192,
        help="Synthetic triadic samples per shell.",
    )
    parser.add_argument("--window", type=int, default=7, help="Abel/log-window width.")
    parser.add_argument("--abel-rho", type=float, default=0.76, help="Abel distance weight rho in [0,1).")
    parser.add_argument(
        "--offdiag-scale",
        type=float,
        default=0.10,
        help="Centered off-diagonal noise scale for good profiles.",
    )
    parser.add_argument(
        "--lln-multiplier",
        type=float,
        default=3.0,
        help="Tolerance multiplier for 1/sqrt(window*samples) proxy LLN scale.",
    )
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.shells < 4:
        raise ValueError("--shells must be at least 4")
    if args.samples_per_shell < 16:
        raise ValueError("--samples-per-shell must be at least 16")
    if args.window <= 1:
        raise ValueError("--window must be greater than 1")
    if args.window > args.shells:
        raise ValueError("--window must not exceed --shells")
    if not (0.0 <= args.abel_rho < 1.0):
        raise ValueError("--abel-rho must satisfy 0 <= rho < 1")
    if args.offdiag_scale < 0.0:
        raise ValueError("--offdiag-scale must be nonnegative")
    if args.lln_multiplier <= 0.0:
        raise ValueError("--lln-multiplier must be positive")


def lambda_value(depth: int) -> float:
    """Positive shell strain proxy with mild deterministic shell variation."""
    phase = 0.73 * depth + 0.17 * math.sin(0.29 * depth)
    return 0.42 + 0.08 * math.sin(phase) + 0.03 * math.cos(1.11 * depth)


def centered(values: Sequence[float]) -> list[float]:
    mean = sum(values) / float(len(values))
    return [value - mean for value in values]


def arcsine_neutral_kappas(samples: int, shell_depth: int, phase_shift: float) -> list[float]:
    # kappa = cos(theta), theta uniform, has the arcsine law on [-1, 1].
    # The half-step grid makes sum cos(2 theta) exactly tiny for the shell.
    return [
        math.cos(2.0 * math.pi * (index + 0.5) / samples + phase_shift + 0.013 * shell_depth)
        for index in range(samples)
    ]


def lln_jittered_kappas(samples: int, shell_depth: int, rng: random.Random) -> list[float]:
    # Stratified arcsine sample with a small deterministic random rotation.
    rotation = rng.random() * 2.0 * math.pi
    return [
        math.cos(
            2.0 * math.pi * (index + 0.5) / samples
            + rotation
            + 0.021 * math.sin(shell_depth + index / max(samples, 1))
        )
        for index in range(samples)
    ]


def bad_correlated_kappas(samples: int, shell_depth: int, lam: float) -> list[float]:
    # Concentrate kappa^2 above 1/2, with a lambda-dependent push.
    target_square = min(0.94, 0.68 + 0.35 * max(0.0, lam - 0.40))
    base = math.sqrt(target_square)
    return [
        base if (index + shell_depth) % 2 == 0 else -base * (0.96 + 0.02 * math.sin(index))
        for index in range(samples)
    ]


def centered_offdiag(samples: int, shell_depth: int, scale: float, phase: float) -> list[float]:
    raw = [
        scale
        * (
            math.sin(1.7 * index + 0.41 * shell_depth + phase)
            + 0.35 * math.cos(0.53 * index - 0.19 * shell_depth)
        )
        for index in range(samples)
    ]
    return centered(raw)


def jittered_centered_offdiag(samples: int, shell_depth: int, scale: float, rng: random.Random) -> list[float]:
    raw = [
        scale
        * (
            rng.uniform(-1.0, 1.0)
            + 0.25 * math.sin(0.37 * shell_depth + 0.91 * index)
        )
        for index in range(samples)
    ]
    return centered(raw)


def bad_offdiag(samples: int, shell_depth: int, lam: float, scale: float) -> list[float]:
    drift = 0.055 + 0.20 * scale + 0.05 * max(0.0, lam - 0.40)
    return [
        drift + 0.015 * math.sin(0.23 * shell_depth + 1.31 * index)
        for index in range(samples)
    ]


def profile_specs(
    *, samples: int, offdiag_scale: float, seed: int
) -> list[tuple[str, str, bool, Callable[[int, float], tuple[list[float], list[float]]]]]:
    rng = random.Random(seed)
    return [
        (
            "lln_exact_arcsine_centered",
            "Arcsine-neutral kappa grid with exactly centered off-diagonal shell noise.",
            True,
            lambda depth, _lam: (
                arcsine_neutral_kappas(samples, depth, phase_shift=0.0),
                centered_offdiag(samples, depth, offdiag_scale, phase=0.0),
            ),
        ),
        (
            "lln_jittered_arcsine_centered",
            "Stratified arcsine samples with shell-dependent jitter and centered off-diagonal noise.",
            True,
            lambda depth, _lam: (
                lln_jittered_kappas(samples, depth, rng),
                jittered_centered_offdiag(samples, depth, offdiag_scale, rng),
            ),
        ),
        (
            "bad_correlated_positive_bias",
            "Deliberately bad profile: kappa^2 is biased above 1/2 and off-diagonal drift is positive.",
            False,
            lambda depth, lam: (
                bad_correlated_kappas(samples, depth, lam),
                bad_offdiag(samples, depth, lam, offdiag_scale),
            ),
        ),
    ]


def build_shell_rows(
    *,
    name: str,
    shells: int,
    samples: int,
    kappa_noise_fn: Callable[[int, float], tuple[list[float], list[float]]],
) -> list[ShellRow]:
    rows: list[ShellRow] = []
    for depth in range(shells):
        lam = lambda_value(depth)
        kappas, offdiag_terms = kappa_noise_fn(depth, lam)
        if len(kappas) != samples or len(offdiag_terms) != samples:
            raise ValueError("profile returned the wrong sample count")
        diagonal_terms = [lam * (2.0 * kappa * kappa - 1.0) for kappa in kappas]
        pointwise_terms = [
            diagonal + offdiag for diagonal, offdiag in zip(diagonal_terms, offdiag_terms)
        ]
        rows.append(
            ShellRow(
                profile=name,
                shell_depth=depth,
                shell_frequency=1 << depth,
                samples=samples,
                lambda_value=lam,
                diagonal_mean=sum(diagonal_terms) / samples,
                offdiag_mean=sum(offdiag_terms) / samples,
                pointwise_proxy_mean=sum(pointwise_terms) / samples,
                diagonal_abs_mean=sum(abs(value) for value in diagonal_terms) / samples,
                offdiag_abs_mean=sum(abs(value) for value in offdiag_terms) / samples,
                shell_lln_scale=1.0 / math.sqrt(samples),
            )
        )
    return rows


def abel_window_weights(width: int, rho: float) -> list[float]:
    center = (width - 1) / 2.0
    raw = [rho ** abs(index - center) for index in range(width)]
    total = sum(raw)
    if total <= EPS:
        raise ValueError("degenerate Abel weights")
    return [value / total for value in raw]


def build_window_rows(
    *,
    name: str,
    shell_rows: Sequence[ShellRow],
    window: int,
    rho: float,
    lln_multiplier: float,
) -> list[AbelWindowRow]:
    weights = abel_window_weights(window, rho)
    half = window // 2
    out: list[AbelWindowRow] = []
    samples = shell_rows[0].samples if shell_rows else 1
    tolerance = lln_multiplier / math.sqrt(max(1, window * samples))
    for center in range(half, len(shell_rows) - (window - half - 1)):
        start = center - half
        stop = start + window
        local = list(shell_rows[start:stop])
        diag = sum(weight * row.diagonal_mean for weight, row in zip(weights, local))
        offdiag = sum(weight * row.offdiag_mean for weight, row in zip(weights, local))
        pointwise = sum(weight * row.pointwise_proxy_mean for weight, row in zip(weights, local))
        abs_diag = sum(weight * row.diagonal_abs_mean for weight, row in zip(weights, local))
        abs_offdiag = sum(weight * row.offdiag_abs_mean for weight, row in zip(weights, local))
        out.append(
            AbelWindowRow(
                profile=name,
                center_depth=center,
                start_depth=start,
                stop_depth=stop - 1,
                window_width=window,
                abel_diagonal_mean=diag,
                abel_offdiag_mean=offdiag,
                abel_pointwise_mean=pointwise,
                abel_abs_diagonal_mean=abs_diag,
                abel_abs_offdiag_mean=abs_offdiag,
                lln_tolerance=tolerance,
                within_lln_tolerance=abs(pointwise) <= tolerance,
            )
        )
    return out


def summarize_profile(
    *,
    name: str,
    description: str,
    expected_good: bool,
    shell_rows: list[ShellRow],
    window_rows: list[AbelWindowRow],
    lln_tolerance: float,
) -> ProfileSummary:
    if not shell_rows or not window_rows:
        raise ValueError("profile must have shell and window rows")
    max_abs_pointwise = max(abs(row.abel_pointwise_mean) for row in window_rows)
    mean_abs_pointwise = sum(abs(row.abel_pointwise_mean) for row in window_rows) / len(window_rows)
    max_abs_diag = max(abs(row.abel_diagonal_mean) for row in window_rows)
    max_abs_offdiag = max(abs(row.abel_offdiag_mean) for row in window_rows)
    fraction_within = sum(1 for row in window_rows if row.within_lln_tolerance) / len(window_rows)

    good_passes = max_abs_pointwise <= lln_tolerance and fraction_within >= 0.90
    bad_visible = (not expected_good) and max_abs_pointwise > 2.0 * lln_tolerance
    if expected_good and good_passes:
        classification = "lln_like_abel_averaging_proxy"
    elif (not expected_good) and bad_visible:
        classification = "bad_correlated_counterprofile"
    else:
        classification = "unexpected_or_borderline_profile"

    checks = {
        "finite_shell_rows": all(
            math.isfinite(row.pointwise_proxy_mean)
            and math.isfinite(row.diagonal_mean)
            and math.isfinite(row.offdiag_mean)
            for row in shell_rows
        ),
        "window_rows_present": bool(window_rows),
        "expected_good_within_lln_tolerance": good_passes if expected_good else True,
        "bad_correlated_profile_visible": bad_visible if not expected_good else True,
        "promotion_false": True,
    }
    return ProfileSummary(
        name=name,
        description=description,
        expected_lln_good=expected_good,
        shell_rows=shell_rows,
        window_rows=window_rows,
        max_abs_abel_pointwise_mean=max_abs_pointwise,
        mean_abs_abel_pointwise_mean=mean_abs_pointwise,
        max_abs_abel_diagonal_mean=max_abs_diag,
        max_abs_abel_offdiag_mean=max_abs_offdiag,
        lln_tolerance=lln_tolerance,
        windows_within_tolerance_fraction=fraction_within,
        classification=classification,
        checks=checks,
    )


def run(
    *,
    shells: int,
    samples_per_shell: int,
    window: int,
    rho: float,
    offdiag_scale: float,
    lln_multiplier: float,
    seed: int,
) -> dict[str, object]:
    tolerance = lln_multiplier / math.sqrt(window * samples_per_shell)
    profiles: list[ProfileSummary] = []
    for name, description, expected_good, builder in profile_specs(
        samples=samples_per_shell,
        offdiag_scale=offdiag_scale,
        seed=seed,
    ):
        shell_rows = build_shell_rows(
            name=name,
            shells=shells,
            samples=samples_per_shell,
            kappa_noise_fn=builder,
        )
        window_rows = build_window_rows(
            name=name,
            shell_rows=shell_rows,
            window=window,
            rho=rho,
            lln_multiplier=lln_multiplier,
        )
        profiles.append(
            summarize_profile(
                name=name,
                description=description,
                expected_good=expected_good,
                shell_rows=shell_rows,
                window_rows=window_rows,
                lln_tolerance=tolerance,
            )
        )

    good_profiles = [profile for profile in profiles if profile.expected_lln_good]
    bad_profiles = [profile for profile in profiles if not profile.expected_lln_good]
    checks = {
        "good_profiles_included": bool(good_profiles),
        "bad_profile_included": bool(bad_profiles),
        "all_good_profiles_pass": all(
            profile.classification == "lln_like_abel_averaging_proxy"
            for profile in good_profiles
        ),
        "bad_profile_fails_visibly": all(
            profile.classification == "bad_correlated_counterprofile"
            for profile in bad_profiles
        ),
        "all_profile_local_checks_pass": all(all(profile.checks.values()) for profile in profiles),
        "promotion_false": True,
    }

    return {
        "harness": "ns_pointwise_to_abel_averaging_proxy",
        "diagnostic_only": True,
        "promotion": False,
        "clay_promoted": False,
        "control": {
            "O": "Local NS A6 pointwise-to-Abel averaging proxy diagnostic.",
            "R": "Simulate diagonal lambda*(2*kappa^2-1), off-diagonal terms, and Abel shell averages.",
            "C": "scripts/ns_pointwise_to_abel_averaging_proxy_harness.py",
            "S": "Synthetic shell model only; no PDE Abel LLN or leakage identity is proved.",
            "L": "shell samples -> diagonal/offdiag means -> Abel windows -> good/bad classification",
            "P": "LLN-like arcsine-neutral profiles should average small; correlated profile should fail visibly.",
            "G": "promotion=false regardless of diagnostic outcome.",
            "F": "Does not prove pointwise-to-Abel replacement for localized NS stretching or any Clay claim.",
        },
        "parameters": {
            "shells": shells,
            "samples_per_shell": samples_per_shell,
            "window": window,
            "abel_rho": rho,
            "offdiag_scale": offdiag_scale,
            "lln_multiplier": lln_multiplier,
            "seed": seed,
            "lln_tolerance": tolerance,
        },
        "summary": {
            "profiles": len(profiles),
            "good_profiles": len(good_profiles),
            "bad_profiles": len(bad_profiles),
            "max_good_abs_abel_pointwise_mean": max(
                profile.max_abs_abel_pointwise_mean for profile in good_profiles
            )
            if good_profiles
            else None,
            "max_bad_abs_abel_pointwise_mean": max(
                profile.max_abs_abel_pointwise_mean for profile in bad_profiles
            )
            if bad_profiles
            else None,
            "lln_tolerance": tolerance,
            "ok": all(checks.values()),
        },
        "checks": checks,
        "profiles": [asdict(profile) for profile in profiles],
        "interpretation": {
            "good_profile_meaning": (
                "Arcsine-neutral kappa samples make lambda*(2*kappa^2-1) shell means small, "
                "and centered off-diagonal terms stay within a 1/sqrt(window*samples) proxy scale."
            ),
            "bad_profile_meaning": (
                "The correlated profile biases kappa^2 above 1/2 and adds positive off-diagonal drift, "
                "so Abel averaging does not remove the pointwise stretching proxy."
            ),
            "non_claims": (
                "No localized Leray commutator estimate, shell mixing theorem, compensated leakage identity, "
                "NS Clay result, YM result, or terminal unification is proved."
            ),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    result = run(
        shells=args.shells,
        samples_per_shell=args.samples_per_shell,
        window=args.window,
        rho=args.abel_rho,
        offdiag_scale=args.offdiag_scale,
        lln_multiplier=args.lln_multiplier,
        seed=args.seed,
    )
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        summary = result["summary"]
        print("NS pointwise-to-Abel averaging proxy harness")
        print(f"wrote: {args.json_output}")
        print(
            "ok={ok} good_max={good} bad_max={bad} tolerance={tol} promotion=false".format(
                ok=summary["ok"],
                good=summary["max_good_abs_abel_pointwise_mean"],
                bad=summary["max_bad_abs_abel_pointwise_mean"],
                tol=summary["lln_tolerance"],
            )
        )
    return 0 if result["summary"]["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
