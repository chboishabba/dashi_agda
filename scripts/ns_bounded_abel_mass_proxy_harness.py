#!/usr/bin/env python3
"""NS bounded Abel-mass proxy harness.

This pure-stdlib diagnostic simulates dyadic shell energies under
Type-I-like envelopes and computes a local Abel/log-window mass proxy.  It is
intended to exercise the A1 bounded-mass bookkeeping surface only:

    Type-I shell envelope  ||P_j U_r||_2 <= M 2^(-j/2)
    proxy shell mass       m_j = 2^j ||P_j U_r||_2^2
    Abel/log-window mass   average of m_j over a local logarithmic window

Bounded profiles should keep the normalized window mass under the configured
constant.  A deliberately bad profile violates the envelope and must be
reported as a visible fail-closed counterprofile.

This script does not construct a PDE defect measure and never promotes Clay,
NS, YM, or unification claims.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


DEFAULT_OUTPUT = Path("outputs/ns_bounded_abel_mass_proxy_harness.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class ShellRow:
    depth: int
    shell: int
    envelope_l2: float
    shell_l2_energy: float
    envelope_ratio: float
    proxy_mass_atom: float


@dataclass(frozen=True)
class WindowRow:
    center_depth: int
    start_depth: int
    stop_depth: int
    window_width: int
    abel_weighted_mass: float
    arithmetic_window_mass: float
    max_atom_mass: float


@dataclass(frozen=True)
class ProfileSummary:
    name: str
    description: str
    expected_bounded: bool
    shell_rows: list[ShellRow]
    window_rows: list[WindowRow]
    max_envelope_ratio: float
    max_proxy_mass_atom: float
    max_abel_window_mass: float
    max_arithmetic_window_mass: float
    mean_abel_window_mass: float
    allowed_atom_mass_bound: float
    allowed_window_mass_bound: float
    bounded_by_envelope: bool
    bounded_by_abel_windows: bool
    classification: str
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shells", type=int, default=28, help="Number of dyadic shell depths.")
    parser.add_argument("--window", type=int, default=9, help="Local logarithmic window width.")
    parser.add_argument("--abel-rho", type=float, default=0.78, help="Abel distance weight rho in [0,1).")
    parser.add_argument("--type-i-bound", type=float, default=1.0, help="Type-I envelope constant M.")
    parser.add_argument(
        "--bad-growth",
        type=float,
        default=0.18,
        help="Positive exponent used by the deliberately bad profile.",
    )
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.shells < 4:
        raise ValueError("--shells must be at least 4")
    if args.window <= 1:
        raise ValueError("--window must be greater than 1")
    if args.window > args.shells:
        raise ValueError("--window must not exceed --shells")
    if not (0.0 <= args.abel_rho < 1.0):
        raise ValueError("--abel-rho must satisfy 0 <= rho < 1")
    if args.type_i_bound <= 0.0:
        raise ValueError("--type-i-bound must be positive")
    if args.bad_growth <= 0.0:
        raise ValueError("--bad-growth must be positive")


def envelope_l2(depth: int, type_i_bound: float) -> float:
    return type_i_bound * (2.0 ** (-0.5 * depth))


def profile_specs(bad_growth: float) -> list[tuple[str, str, bool, Callable[[int], float]]]:
    return [
        (
            "critical_type_i_envelope",
            "Saturates the model envelope ||P_j U||_2 = M 2^(-j/2).",
            True,
            lambda depth: 1.0,
        ),
        (
            "log_depleted_type_i",
            "Strictly bounded Type-I-like profile with mild logarithmic depletion.",
            True,
            lambda depth: 1.0 / math.sqrt(depth + 2.0),
        ),
        (
            "oscillatory_bounded_type_i",
            "Bounded envelope with deterministic low-amplitude shell oscillation.",
            True,
            lambda depth: 0.82 + 0.14 * math.sin(0.9 * depth),
        ),
        (
            "bad_supercritical_growth",
            "Deliberately bad profile: envelope ratio grows exponentially with depth.",
            False,
            lambda depth: 2.0 ** (bad_growth * depth),
        ),
    ]


def build_shell_rows(
    *,
    shells: int,
    type_i_bound: float,
    ratio_fn: Callable[[int], float],
) -> list[ShellRow]:
    rows: list[ShellRow] = []
    for depth in range(shells):
        shell = 1 << depth
        env = envelope_l2(depth, type_i_bound)
        ratio = max(0.0, ratio_fn(depth))
        energy = env * ratio
        atom_mass = float(shell) * energy * energy
        rows.append(
            ShellRow(
                depth=depth,
                shell=shell,
                envelope_l2=env,
                shell_l2_energy=energy,
                envelope_ratio=ratio,
                proxy_mass_atom=atom_mass,
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


def build_window_rows(rows: Sequence[ShellRow], window: int, rho: float) -> list[WindowRow]:
    weights = abel_window_weights(window, rho)
    half = window // 2
    out: list[WindowRow] = []
    for center in range(half, len(rows) - (window - half - 1)):
        start = center - half
        stop = start + window
        window_rows = list(rows[start:stop])
        masses = [row.proxy_mass_atom for row in window_rows]
        abel_mass = sum(weight * mass for weight, mass in zip(weights, masses))
        arithmetic_mass = sum(masses) / float(window)
        out.append(
            WindowRow(
                center_depth=center,
                start_depth=start,
                stop_depth=stop - 1,
                window_width=window,
                abel_weighted_mass=abel_mass,
                arithmetic_window_mass=arithmetic_mass,
                max_atom_mass=max(masses),
            )
        )
    return out


def summarize_profile(
    *,
    name: str,
    description: str,
    expected_bounded: bool,
    shell_rows: list[ShellRow],
    window_rows: list[WindowRow],
    type_i_bound: float,
) -> ProfileSummary:
    if not shell_rows or not window_rows:
        raise ValueError("profile must have shell and window rows")
    allowed_atom = type_i_bound * type_i_bound
    allowed_window = allowed_atom
    max_ratio = max(row.envelope_ratio for row in shell_rows)
    max_atom = max(row.proxy_mass_atom for row in shell_rows)
    max_abel = max(row.abel_weighted_mass for row in window_rows)
    max_arithmetic = max(row.arithmetic_window_mass for row in window_rows)
    mean_abel = sum(row.abel_weighted_mass for row in window_rows) / len(window_rows)
    bounded_by_envelope = max_ratio <= 1.0 + 1.0e-10
    bounded_by_windows = max_abel <= allowed_window * (1.0 + 1.0e-10)
    if expected_bounded and bounded_by_envelope and bounded_by_windows:
        classification = "bounded_type_i_proxy"
    elif (not expected_bounded) and (not bounded_by_envelope) and (not bounded_by_windows):
        classification = "bad_unbounded_counterprofile"
    else:
        classification = "unexpected_or_borderline_profile"
    checks = {
        "finite_nonnegative_shell_masses": all(
            math.isfinite(row.proxy_mass_atom) and row.proxy_mass_atom >= 0.0 for row in shell_rows
        ),
        "window_rows_present": bool(window_rows),
        "expected_bounded_classification": classification == "bounded_type_i_proxy"
        if expected_bounded
        else True,
        "bad_profile_violation_visible": classification == "bad_unbounded_counterprofile"
        if not expected_bounded
        else True,
        "promotion_false": True,
    }
    return ProfileSummary(
        name=name,
        description=description,
        expected_bounded=expected_bounded,
        shell_rows=shell_rows,
        window_rows=window_rows,
        max_envelope_ratio=max_ratio,
        max_proxy_mass_atom=max_atom,
        max_abel_window_mass=max_abel,
        max_arithmetic_window_mass=max_arithmetic,
        mean_abel_window_mass=mean_abel,
        allowed_atom_mass_bound=allowed_atom,
        allowed_window_mass_bound=allowed_window,
        bounded_by_envelope=bounded_by_envelope,
        bounded_by_abel_windows=bounded_by_windows,
        classification=classification,
        checks=checks,
    )


def run(*, shells: int, window: int, rho: float, type_i_bound: float, bad_growth: float) -> dict[str, object]:
    profiles: list[ProfileSummary] = []
    for name, description, expected_bounded, ratio_fn in profile_specs(bad_growth):
        shell_rows = build_shell_rows(shells=shells, type_i_bound=type_i_bound, ratio_fn=ratio_fn)
        window_rows = build_window_rows(shell_rows, window=window, rho=rho)
        profiles.append(
            summarize_profile(
                name=name,
                description=description,
                expected_bounded=expected_bounded,
                shell_rows=shell_rows,
                window_rows=window_rows,
                type_i_bound=type_i_bound,
            )
        )

    bounded_profiles = [profile for profile in profiles if profile.expected_bounded]
    bad_profiles = [profile for profile in profiles if not profile.expected_bounded]
    checks = {
        "all_bounded_profiles_pass": all(
            profile.bounded_by_envelope and profile.bounded_by_abel_windows for profile in bounded_profiles
        ),
        "bad_profile_included": bool(bad_profiles),
        "bad_profile_violates_boundedness": any(
            (not profile.bounded_by_envelope) and (not profile.bounded_by_abel_windows)
            for profile in bad_profiles
        ),
        "all_profile_local_checks_pass": all(all(profile.checks.values()) for profile in profiles),
        "promotion_false": True,
    }

    return {
        "harness": "ns_bounded_abel_mass_proxy",
        "diagnostic_only": True,
        "promotion": False,
        "clay_promoted": False,
        "control": {
            "O": "Local NS A1 bounded Abel-mass proxy diagnostic.",
            "R": "Simulate Type-I-like shell energies and detect Abel/log-window boundedness.",
            "C": "scripts/ns_bounded_abel_mass_proxy_harness.py",
            "S": "Synthetic shell model only; no PDE Abel measure is constructed.",
            "L": "shell envelope -> proxy mass atoms -> Abel/log windows -> fail-closed classification",
            "P": "Bounded Type-I profiles must pass; deliberate bad profile must visibly fail.",
            "G": "promotion=false regardless of diagnostic outcome.",
            "F": "Does not prove A1 bounded mass for CKN-scale rescalings or any Clay claim.",
        },
        "parameters": {
            "shells": shells,
            "window": window,
            "abel_rho": rho,
            "type_i_bound": type_i_bound,
            "bad_growth": bad_growth,
        },
        "summary": {
            "profiles": len(profiles),
            "bounded_profiles": len(bounded_profiles),
            "bad_profiles": len(bad_profiles),
            "max_bounded_abel_window_mass": max(
                profile.max_abel_window_mass for profile in bounded_profiles
            )
            if bounded_profiles
            else None,
            "max_bad_abel_window_mass": max(profile.max_abel_window_mass for profile in bad_profiles)
            if bad_profiles
            else None,
            "allowed_window_mass_bound": type_i_bound * type_i_bound,
            "ok": all(checks.values()),
        },
        "checks": checks,
        "profiles": [asdict(profile) for profile in profiles],
        "interpretation": {
            "bounded_mass_proxy_meaning": (
                "For profiles satisfying ||P_j U||_2 <= M 2^(-j/2), "
                "2^j||P_j U||_2^2 and its normalized Abel/log-window averages stay <= M^2."
            ),
            "bad_profile_meaning": (
                "The supercritical profile violates the envelope and the Abel/log-window mass bound, "
                "so the diagnostic is fail-closed rather than permissive."
            ),
            "non_claims": (
                "No CKN-scale PDE defect measure, stationarity theorem, compensated leakage identity, "
                "NS Clay result, YM result, or unification promotion is proved."
            ),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    result = run(
        shells=args.shells,
        window=args.window,
        rho=args.abel_rho,
        type_i_bound=args.type_i_bound,
        bad_growth=args.bad_growth,
    )
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        summary = result["summary"]
        print("NS bounded Abel-mass proxy harness")
        print(f"wrote: {args.json_output}")
        print(
            "ok={ok} bounded_max={bounded} bad_max={bad} promotion=false".format(
                ok=summary["ok"],
                bounded=summary["max_bounded_abel_window_mass"],
                bad=summary["max_bad_abel_window_mass"],
            )
        )
    return 0 if result["summary"]["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
