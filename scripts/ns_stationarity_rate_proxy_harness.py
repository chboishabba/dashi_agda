#!/usr/bin/env python3
"""NS stationarity-rate proxy harness.

This pure-stdlib diagnostic simulates a finite dyadic stationarity-rate surface
with

    theta_r ~= log(1/r)^(-1/2)

and propagates a simple Gronwall/Lipschitz stationarity defect delta_r.  It is
only a code harness: no PDE measure is constructed and promotion is always
false.  One profile is deliberately bad, with a nondecaying control term, so
the JSON receipt records a visible fail-closed counterprofile.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


DEFAULT_OUTPUT = Path("outputs/ns_stationarity_rate_proxy_harness.json")
BIAS_CONSTANT = math.sqrt(11.0 / 60.0)
EPS = 1.0e-12


@dataclass(frozen=True)
class RateRow:
    depth: int
    r: float
    log_inv_r: float
    theta_r: float
    control_r: float
    gronwall_gain: float
    memory_factor: float
    lipschitz_increment: float
    delta_r: float
    bias_bound: float


@dataclass(frozen=True)
class ProfileSummary:
    name: str
    description: str
    rows: list[RateRow]
    initial_delta: float
    terminal_delta: float
    terminal_theta: float
    terminal_control: float
    terminal_bias_bound: float
    delta_ratio_last_first: float
    delta_ratio_last_tail_start: float
    control_ratio_last_first: float
    theta_ratio_last_first: float
    empirical_delta_log_slope: float
    classification: str
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", type=int, default=10, help="Number of dyadic r-depths.")
    parser.add_argument("--min-depth", type=int, default=2, help="First dyadic depth, r=2^-depth.")
    parser.add_argument("--theta-scale", type=float, default=1.0)
    parser.add_argument("--lipschitz", type=float, default=0.35)
    parser.add_argument("--dt", type=float, default=0.25)
    parser.add_argument("--memory-decay", type=float, default=2.4)
    parser.add_argument("--initial-delta", type=float, default=0.0)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.depths <= 1:
        raise ValueError("--depths must be greater than 1")
    if args.min_depth <= 0:
        raise ValueError("--min-depth must be positive")
    if args.theta_scale <= 0.0:
        raise ValueError("--theta-scale must be positive")
    if args.lipschitz < 0.0:
        raise ValueError("--lipschitz must be nonnegative")
    if args.dt <= 0.0:
        raise ValueError("--dt must be positive")
    if args.memory_decay < 0.0:
        raise ValueError("--memory-decay must be nonnegative")
    if args.initial_delta < 0.0:
        raise ValueError("--initial-delta must be nonnegative")


def theta_rate(log_inv_r: float, theta_scale: float) -> float:
    if log_inv_r <= 0.0:
        raise ValueError("log(1/r) must be positive")
    return theta_scale / math.sqrt(log_inv_r)


def profile_specs() -> list[tuple[str, str, Callable[[float, float, int], float], bool]]:
    return [
        (
            "log_square_control",
            "Decaying control c_r = 0.35 * theta_r^2.",
            lambda theta, _log_inv_r, _depth: 0.35 * theta * theta,
            True,
        ),
        (
            "log_32_control",
            "Decaying control c_r = 0.20 * log(1/r)^(-3/2).",
            lambda _theta, log_inv_r, _depth: 0.20 / (log_inv_r ** 1.5),
            True,
        ),
        (
            "lipschitz_matched_control",
            "Mild control c_r = 0.12 * theta_r on the same log-rate scale.",
            lambda theta, _log_inv_r, _depth: 0.12 * theta,
            True,
        ),
        (
            "bad_nondecaying_control",
            "Deliberately bad profile with c_r = 0.20 independent of r.",
            lambda _theta, _log_inv_r, _depth: 0.20,
            False,
        ),
    ]


def empirical_log_slope(rows: Sequence[RateRow]) -> float:
    if len(rows) < 2:
        return 0.0
    first = rows[0]
    last = rows[-1]
    if first.delta_r <= EPS or last.delta_r <= EPS:
        return 0.0
    logx_first = math.log(first.log_inv_r)
    logx_last = math.log(last.log_inv_r)
    if abs(logx_last - logx_first) <= EPS:
        return 0.0
    return (math.log(last.delta_r) - math.log(first.delta_r)) / (logx_last - logx_first)


def propagate_profile(
    *,
    name: str,
    description: str,
    control_fn: Callable[[float, float, int], float],
    expected_decaying: bool,
    depths: int,
    min_depth: int,
    theta_scale: float,
    lipschitz: float,
    dt: float,
    memory_decay: float,
    initial_delta: float,
) -> ProfileSummary:
    rows: list[RateRow] = []
    previous_delta = initial_delta
    gronwall_gain = math.exp(lipschitz * dt)
    memory_factor = math.exp(-memory_decay * dt)

    for offset in range(depths):
        depth = min_depth + offset
        r = 2.0 ** (-depth)
        log_inv_r = math.log(1.0 / r)
        theta = theta_rate(log_inv_r=log_inv_r, theta_scale=theta_scale)
        control = max(0.0, control_fn(theta, log_inv_r, depth))
        lipschitz_increment = dt * (lipschitz * theta + control)
        delta = gronwall_gain * (memory_factor * previous_delta + lipschitz_increment)
        rows.append(
            RateRow(
                depth=depth,
                r=r,
                log_inv_r=log_inv_r,
                theta_r=theta,
                control_r=control,
                gronwall_gain=gronwall_gain,
                memory_factor=memory_factor,
                lipschitz_increment=lipschitz_increment,
                delta_r=delta,
                bias_bound=delta * BIAS_CONSTANT,
            )
        )
        previous_delta = delta

    first = rows[0]
    last = rows[-1]
    tail_start = rows[min(3, len(rows) - 1)]
    delta_ratio = last.delta_r / max(first.delta_r, EPS)
    tail_delta_ratio = last.delta_r / max(tail_start.delta_r, EPS)
    control_ratio = last.control_r / max(first.control_r, EPS)
    theta_ratio = last.theta_r / max(first.theta_r, EPS)
    slope = empirical_log_slope(rows)
    nonincreasing_theta = all(
        rows[index + 1].theta_r <= rows[index].theta_r + EPS for index in range(len(rows) - 1)
    )
    bias_formula_ok = all(
        abs(row.bias_bound - row.delta_r * BIAS_CONSTANT) < 1.0e-12 for row in rows
    )
    finite_nonnegative = all(
        math.isfinite(row.delta_r) and row.delta_r >= 0.0 and math.isfinite(row.bias_bound)
        for row in rows
    )
    control_decays = control_ratio < 0.80
    delta_tracks_log_rate = tail_delta_ratio < 0.90
    bad_nondecay_visible = (not expected_decaying) and control_ratio > 0.95 and delta_ratio > 0.90
    checks = {
        "theta_r_log_minus_half_nonincreasing": nonincreasing_theta,
        "finite_nonnegative_delta_and_bias": finite_nonnegative,
        "bias_bound_matches_delta_sqrt_11_60": bias_formula_ok,
        "expected_control_decay": control_decays if expected_decaying else True,
        "expected_delta_decay": delta_tracks_log_rate if expected_decaying else True,
        "bad_nondecaying_control_visible": bad_nondecay_visible if not expected_decaying else True,
        "promotion_false": True,
    }
    if not expected_decaying:
        classification = "bad_nondecaying_counterprofile"
    elif delta_tracks_log_rate:
        classification = "decaying_stationarity_proxy"
    else:
        classification = "slow_or_unresolved_stationarity_proxy"

    return ProfileSummary(
        name=name,
        description=description,
        rows=rows,
        initial_delta=initial_delta,
        terminal_delta=last.delta_r,
        terminal_theta=last.theta_r,
        terminal_control=last.control_r,
        terminal_bias_bound=last.bias_bound,
        delta_ratio_last_first=delta_ratio,
        delta_ratio_last_tail_start=tail_delta_ratio,
        control_ratio_last_first=control_ratio,
        theta_ratio_last_first=theta_ratio,
        empirical_delta_log_slope=slope,
        classification=classification,
        checks=checks,
    )


def run(
    *,
    depths: int,
    min_depth: int,
    theta_scale: float,
    lipschitz: float,
    dt: float,
    memory_decay: float,
    initial_delta: float,
) -> dict[str, object]:
    profiles = [
        propagate_profile(
            name=name,
            description=description,
            control_fn=control_fn,
            expected_decaying=expected_decaying,
            depths=depths,
            min_depth=min_depth,
            theta_scale=theta_scale,
            lipschitz=lipschitz,
            dt=dt,
            memory_decay=memory_decay,
            initial_delta=initial_delta,
        )
        for name, description, control_fn, expected_decaying in profile_specs()
    ]
    checks = {
        "all_bias_bounds_match": all(
            profile.checks["bias_bound_matches_delta_sqrt_11_60"] for profile in profiles
        ),
        "all_good_profiles_decay": all(
            profile.checks["expected_delta_decay"]
            for profile in profiles
            if profile.classification != "bad_nondecaying_counterprofile"
        ),
        "bad_nondecaying_profile_included": any(
            profile.classification == "bad_nondecaying_counterprofile" for profile in profiles
        ),
        "bad_nondecaying_profile_visible": all(
            profile.checks["bad_nondecaying_control_visible"]
            for profile in profiles
            if profile.classification == "bad_nondecaying_counterprofile"
        ),
        "promotion_false": True,
    }
    return {
        "ok": all(checks.values()),
        "script": "scripts/ns_stationarity_rate_proxy_harness.py",
        "scope": "finite_synthetic_stationarity_rate_proxy_not_pde_proof",
        "rate_model": {
            "r_grid": "r=2^-depth",
            "theta_r": "theta_scale / sqrt(log(1/r))",
            "delta_update": "delta_i = exp(L*dt) * (exp(-memory_decay*dt)*delta_{i-1} + dt*(L*theta_i + control_i))",
            "bias_bound": "delta_r * sqrt(11/60)",
        },
        "parameters": {
            "depths": depths,
            "min_depth": min_depth,
            "theta_scale": theta_scale,
            "lipschitz": lipschitz,
            "dt": dt,
            "memory_decay": memory_decay,
            "initial_delta": initial_delta,
            "bias_constant_sqrt_11_60": BIAS_CONSTANT,
        },
        "profiles": [asdict(profile) for profile in profiles],
        "checks": checks,
        "promotion": False,
        "promotion_false": True,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    payload = run(
        depths=args.depths,
        min_depth=args.min_depth,
        theta_scale=args.theta_scale,
        lipschitz=args.lipschitz,
        dt=args.dt,
        memory_decay=args.memory_decay,
        initial_delta=args.initial_delta,
    )
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    if args.json:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
