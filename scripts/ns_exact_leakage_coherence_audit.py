#!/usr/bin/env python3
"""Finite exact-Leray leakage/coherence audit for NS triads.

This is a local diagnostic harness only.  It samples exact finite
Leray-vorticity triads using ``ns_exact_strain_eigenbundle.py``, computes the
output velocity/vorticity/strain frame, and splits the output velocity energy
against several candidate coherent channels.

The important A/B check is:

* ``output_locked_velocity`` is non-propagated and tautological, so leakage is
  zero up to roundoff.
* propagated channels remember input velocity/vorticity data before projecting
  to the output tangent plane, so nontrivial leakage is expected generically.

The checked identity is only the finite orthogonal/Plancherel-style split

    |u_c|^2 = |Pi_channel u_c|^2 + |(I-Pi_channel) u_c|^2.

It proves no PDE sign estimate, no compensated leakage theorem, and no
Navier-Stokes/Clay promotion.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import ns_exact_strain_eigenbundle as exact  # noqa: E402


Vec3 = tuple[float, float, float]
EPS = 1.0e-12


CHANNELS = (
    "output_locked_velocity",
    "canonical_output_tangent",
    "propagated_velocity_mean",
    "propagated_vorticity_mean_velocity",
    "propagated_input_vorticity_cross",
)


@dataclass(frozen=True)
class ChannelStats:
    attempted_rows: int = 0
    usable_rows: int = 0
    missing_channel_rows: int = 0
    energy_sum: float = 0.0
    coherent_energy_sum: float = 0.0
    leakage_energy_sum: float = 0.0
    lambda_weighted_energy_sum: float = 0.0
    min_lambda: float | None = None
    mean_lambda: float | None = None
    median_lambda: float | None = None
    p95_lambda: float | None = None
    max_lambda: float | None = None
    nontrivial_leakage_rows: int = 0
    nontrivial_leakage_fraction: float | None = None
    max_split_error: float = 0.0
    split_identity_error: float = 0.0
    lambda_identity_error: float = 0.0


@dataclass(frozen=True)
class SampleRow:
    index: int
    rho: float
    c_norm: float
    output_energy: float
    output_vorticity_norm: float
    output_locked_lambda: float
    propagated_velocity_mean_lambda: float | None
    propagated_vorticity_mean_velocity_lambda: float | None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--rho-min", type=float, default=0.25)
    parser.add_argument("--rho-max", type=float, default=4.0)
    parser.add_argument("--near-resonance-threshold", type=float, default=1.0e-8)
    parser.add_argument("--leakage-threshold", type=float, default=1.0e-3)
    parser.add_argument("--symmetrized", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--sample-rows", type=int, default=5)
    parser.add_argument("--json-output", type=Path, default=None)
    return parser.parse_args()


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def quantile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[index]


def finite(value: float | None) -> float | None:
    if value is None:
        return None
    if math.isnan(value) or math.isinf(value):
        return None
    return float(value)


def unit_or_none(v: Vec3 | None) -> Vec3 | None:
    if v is None:
        return None
    return exact.normalize(v)


def tangent_unit(c: Vec3, v: Vec3) -> Vec3 | None:
    projected = exact.project_onto_plane(c, v)
    if projected is None:
        return None
    return exact.normalize(projected)


def velocity_from_output_vorticity(c: Vec3, omega: Vec3) -> Vec3 | None:
    """Convert an output tangent vorticity direction into a velocity channel.

    For unit directions, Biot-Savart is equivalent up to sign to ``c x omega``.
    The sign does not matter for a one-dimensional projection.
    """

    c_hat = exact.normalize(c)
    if c_hat is None:
        return None
    return exact.normalize(exact.cross(c_hat, omega))


def channel_vector(
    name: str,
    velocity: exact.TriadVelocityOutput,
    strain: exact.StrainEigenbundle,
) -> Vec3 | None:
    c = velocity.c
    if name == "output_locked_velocity":
        return exact.normalize(velocity.u_c)

    if name == "canonical_output_tangent":
        return exact.vorticity_polarization(c, "e1")

    if name == "propagated_velocity_mean":
        u_a = unit_or_none(velocity.u_a)
        u_b = unit_or_none(velocity.u_b)
        if u_a is None or u_b is None:
            return None
        return tangent_unit(c, exact.add(u_a, u_b))

    if name == "propagated_vorticity_mean_velocity":
        omega_memory = tangent_unit(c, exact.add(velocity.omega_a, velocity.omega_b))
        if omega_memory is None:
            return None
        return velocity_from_output_vorticity(c, omega_memory)

    if name == "propagated_input_vorticity_cross":
        omega_cross = tangent_unit(c, exact.cross(velocity.omega_a, velocity.omega_b))
        if omega_cross is None:
            return None
        return velocity_from_output_vorticity(c, omega_cross)

    raise ValueError(f"unknown channel: {name}")


def split_against_channel(output: Vec3, channel: Vec3) -> dict[str, float]:
    channel_unit = exact.normalize(channel)
    if channel_unit is None:
        raise ValueError("channel must be nonzero")
    output_energy = exact.norm_sq(output)
    coherent = exact.scale(exact.dot(output, channel_unit), channel_unit)
    leakage = exact.sub(output, coherent)
    coherent_energy = exact.norm_sq(coherent)
    leakage_energy = exact.norm_sq(leakage)
    lambda_fraction = leakage_energy / output_energy if output_energy > EPS else 0.0
    return {
        "output_energy": output_energy,
        "coherent_energy": coherent_energy,
        "leakage_energy": leakage_energy,
        "lambda_fraction": lambda_fraction,
        "split_error": abs(output_energy - coherent_energy - leakage_energy),
        "lambda_weighted_energy": lambda_fraction * output_energy,
    }


def summarize_channel(
    attempted_rows: int,
    values: list[dict[str, float]],
    missing_rows: int,
    leakage_threshold: float,
) -> ChannelStats:
    if not values:
        return ChannelStats(
            attempted_rows=attempted_rows,
            usable_rows=0,
            missing_channel_rows=missing_rows,
        )

    lambdas = [row["lambda_fraction"] for row in values]
    energy_sum = sum(row["output_energy"] for row in values)
    coherent_sum = sum(row["coherent_energy"] for row in values)
    leakage_sum = sum(row["leakage_energy"] for row in values)
    lambda_weighted_sum = sum(row["lambda_weighted_energy"] for row in values)
    nontrivial = sum(1 for value in lambdas if value > leakage_threshold)
    return ChannelStats(
        attempted_rows=attempted_rows,
        usable_rows=len(values),
        missing_channel_rows=missing_rows,
        energy_sum=energy_sum,
        coherent_energy_sum=coherent_sum,
        leakage_energy_sum=leakage_sum,
        lambda_weighted_energy_sum=lambda_weighted_sum,
        min_lambda=quantile(lambdas, 0.0),
        mean_lambda=sum(lambdas) / len(lambdas),
        median_lambda=quantile(lambdas, 0.5),
        p95_lambda=quantile(lambdas, 0.95),
        max_lambda=quantile(lambdas, 1.0),
        nontrivial_leakage_rows=nontrivial,
        nontrivial_leakage_fraction=nontrivial / len(values),
        max_split_error=max(row["split_error"] for row in values),
        split_identity_error=abs(energy_sum - coherent_sum - leakage_sum),
        lambda_identity_error=abs(lambda_weighted_sum - leakage_sum),
    )


def build_bundle(
    rng: random.Random,
    index: int,
    rho_min: float,
    rho_max: float,
    near_resonance_threshold: float,
    symmetrized: bool,
) -> tuple[float, exact.TriadicStrainEigenbundle] | None:
    models = ("e1", "e2", "plus45", "minus45", "angle")
    for _ in range(128):
        rho = rng.uniform(rho_min, rho_max)
        a = exact.scale(rho, random_unit(rng))
        b = random_unit(rng)
        if exact.norm(exact.add(a, b)) <= near_resonance_threshold:
            continue
        model_a = models[index % len(models)]
        model_b = models[(index + 2) % len(models)]
        omega_a = exact.vorticity_polarization(
            a,
            model_a,
            angle=rng.uniform(0.0, 2.0 * math.pi),
        )
        omega_b = exact.vorticity_polarization(
            b,
            model_b,
            angle=rng.uniform(0.0, 2.0 * math.pi),
        )
        if omega_a is None or omega_b is None:
            continue
        bundle = exact.triadic_strain_eigenbundle(
            a,
            b,
            omega_a,
            omega_b,
            symmetrized=symmetrized,
        )
        if bundle is not None:
            return rho, bundle
    return None


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.rho_min <= 0.0 or args.rho_max <= 0.0 or args.rho_min > args.rho_max:
        raise SystemExit("--rho-min/--rho-max must be positive and ordered")
    if args.leakage_threshold < 0.0:
        raise SystemExit("--leakage-threshold must be nonnegative")

    rng = random.Random(args.seed)
    channel_values: dict[str, list[dict[str, float]]] = {name: [] for name in CHANNELS}
    channel_missing: dict[str, int] = {name: 0 for name in CHANNELS}
    rows: list[SampleRow] = []
    degenerate_rows = 0
    max_output_divergence = 0.0
    max_output_vorticity_dot_c = 0.0
    max_output_vorticity_dot_u = 0.0

    for index in range(args.samples):
        built = build_bundle(
            rng,
            index,
            args.rho_min,
            args.rho_max,
            args.near_resonance_threshold,
            args.symmetrized,
        )
        if built is None:
            degenerate_rows += 1
            continue

        rho, bundle = built
        velocity = bundle.velocity
        strain = bundle.strain
        output = velocity.u_c
        max_output_divergence = max(
            max_output_divergence,
            abs(exact.dot(exact.normalize(velocity.c) or velocity.c, output)),
        )
        max_output_vorticity_dot_c = max(
            max_output_vorticity_dot_c,
            abs(exact.dot(strain.c_hat, strain.omega_out)),
        )
        max_output_vorticity_dot_u = max(
            max_output_vorticity_dot_u,
            abs(exact.dot(strain.u_hat, strain.omega_out)),
        )

        row_lambdas: dict[str, float | None] = {}
        for channel in CHANNELS:
            vector = channel_vector(channel, velocity, strain)
            if vector is None:
                channel_missing[channel] += 1
                row_lambdas[channel] = None
                continue
            split = split_against_channel(output, vector)
            channel_values[channel].append(split)
            row_lambdas[channel] = split["lambda_fraction"]

        if len(rows) < args.sample_rows:
            rows.append(
                SampleRow(
                    index=index,
                    rho=rho,
                    c_norm=exact.norm(velocity.c),
                    output_energy=exact.norm_sq(output),
                    output_vorticity_norm=exact.norm(strain.omega_out),
                    output_locked_lambda=float(row_lambdas["output_locked_velocity"] or 0.0),
                    propagated_velocity_mean_lambda=finite(
                        row_lambdas["propagated_velocity_mean"]
                    ),
                    propagated_vorticity_mean_velocity_lambda=finite(
                        row_lambdas["propagated_vorticity_mean_velocity"]
                    ),
                )
            )

    accepted_rows = args.samples - degenerate_rows
    channel_stats = {
        name: asdict(
            summarize_channel(
                attempted_rows=accepted_rows,
                values=channel_values[name],
                missing_rows=channel_missing[name],
                leakage_threshold=args.leakage_threshold,
            )
        )
        for name in CHANNELS
    }
    output_locked_mean = channel_stats["output_locked_velocity"]["mean_lambda"]
    propagated_means = {
        name: channel_stats[name]["mean_lambda"]
        for name in CHANNELS
        if name.startswith("propagated_")
    }
    propagated_nontrivial = {
        name: channel_stats[name]["nontrivial_leakage_fraction"]
        for name in CHANNELS
        if name.startswith("propagated_")
    }
    split_pass = all(
        stats["max_split_error"] <= 1.0e-10 and stats["lambda_identity_error"] <= 1.0e-10
        for stats in channel_stats.values()
        if stats["usable_rows"] > 0
    )
    nontrivial_under_propagation = any(
        (value is not None and value > 0.25) for value in propagated_nontrivial.values()
    )

    return {
        "contract": "ns_exact_leakage_coherence_audit",
        "scope": "finite_exact_leray_vorticity_triad_diagnostic_only_not_pde_proof",
        "seed": args.seed,
        "parameters": {
            "samples": args.samples,
            "rho_min": args.rho_min,
            "rho_max": args.rho_max,
            "near_resonance_threshold": args.near_resonance_threshold,
            "leakage_threshold": args.leakage_threshold,
            "symmetrized": args.symmetrized,
        },
        "rows": {
            "accepted": accepted_rows,
            "degenerate_or_resampled_out": degenerate_rows,
        },
        "channels": channel_stats,
        "comparisons": {
            "output_locked_mean_lambda": output_locked_mean,
            "propagated_mean_lambdas": propagated_means,
            "propagated_nontrivial_leakage_fractions": propagated_nontrivial,
            "nontrivial_leakage_under_some_propagated_choice": nontrivial_under_propagation,
        },
        "invariants": {
            "max_output_divergence_abs": max_output_divergence,
            "max_output_vorticity_dot_c_abs": max_output_vorticity_dot_c,
            "max_output_vorticity_dot_u_abs": max_output_vorticity_dot_u,
            "plancherel_style_splits_pass": split_pass,
        },
        "sample_rows": [asdict(row) for row in rows],
        "promotion": False,
        "clay_navier_stokes_promoted": False,
        "pde_residual_sign_proved": False,
        "triadic_compensated_leakage_identity_proved": False,
        "interpretation": (
            "output_locked_velocity is a tautological non-propagated channel; "
            "propagated channels are finite input-memory coherence diagnostics. "
            "Nontrivial propagated leakage is evidence the audit can distinguish "
            "coherence choices, not evidence of an NS PDE sign theorem."
        ),
    }


def main() -> int:
    args = parse_args()
    report = run(args)
    text = json.dumps(report, indent=2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)
    split_pass = bool(report["invariants"]["plancherel_style_splits_pass"])
    return 0 if split_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
