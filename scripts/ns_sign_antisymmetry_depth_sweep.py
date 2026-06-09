#!/usr/bin/env python3
"""Exact finite NS sign-antisymmetry/depth-k cascade sweep.

This is a bounded local calculation harness.  It samples exact finite
Leray-vorticity triads, checks the algebraic sign antisymmetry identity

    (a . omega_c) + (b . omega_c) = (a + b) . omega_c = 0,

where ``omega_c`` is the output vorticity direction, and follows zero-mode-ish
cascade survivors under a configurable coherence/leakage threshold.

The sweep is finite-symbol diagnostics only.  It proves no PDE residual sign,
no output-width theorem, no compensated leakage theorem, and no Clay result.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


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
class CascadeState:
    frequency: Vec3
    omega: Vec3


@dataclass(frozen=True)
class DepthStats:
    depth: int
    attempted_triads: int
    accepted_triads: int
    survivors: int
    survivor_fraction_of_accepted: float | None
    output_width: float | None
    output_width_witness: Vec3 | None
    min_leakage: float | None
    median_leakage: float | None
    p95_leakage: float | None
    max_leakage: float | None
    max_sign_identity_abs: float
    mean_sign_identity_abs: float | None
    max_relative_sign_identity_abs: float
    max_output_divergence_abs: float
    max_omega_c_dot_c_abs: float


@dataclass(frozen=True)
class SampleSurvivor:
    depth: int
    leakage_fraction: float
    sign_identity_abs: float
    output_direction: Vec3


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--continuations", type=int, default=1)
    parser.add_argument("--max-paths-per-depth", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--rho-min", type=float, default=0.25)
    parser.add_argument("--rho-max", type=float, default=4.0)
    parser.add_argument("--zero-mode-threshold", type=float, default=0.05)
    parser.add_argument("--near-resonance-threshold", type=float, default=1.0e-8)
    parser.add_argument("--symmetrized", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--coherence-channel", choices=CHANNELS, default="propagated_velocity_mean")
    parser.add_argument("--normals", type=int, default=512)
    parser.add_argument("--sample-survivors", type=int, default=8)
    parser.add_argument("--json-output", type=Path, default=None)
    return parser.parse_args()


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    radius = math.sqrt(max(0.0, 1.0 - z * z))
    return (radius * math.cos(theta), radius * math.sin(theta), z)


def random_frequency(rng: random.Random, rho_min: float, rho_max: float) -> Vec3:
    return exact.scale(rng.uniform(rho_min, rho_max), random_unit(rng))


def random_vorticity_for_frequency(rng: random.Random, frequency: Vec3) -> Vec3 | None:
    basis = exact.tangent_basis(frequency)
    if basis is None:
        return None
    angle = rng.uniform(0.0, 2.0 * math.pi)
    return exact.normalize(
        exact.add(
            exact.scale(math.cos(angle), basis.e1),
            exact.scale(math.sin(angle), basis.e2),
        )
    )


def fibonacci_sphere(count: int) -> list[Vec3]:
    if count <= 0:
        return []
    points: list[Vec3] = []
    golden_angle = math.pi * (3.0 - math.sqrt(5.0))
    for i in range(count):
        z = 1.0 - (2.0 * (i + 0.5) / count)
        radius = math.sqrt(max(0.0, 1.0 - z * z))
        theta = golden_angle * i
        points.append((radius * math.cos(theta), radius * math.sin(theta), z))
    return points


def estimate_width(outputs: list[Vec3], normals: list[Vec3]) -> tuple[float | None, Vec3 | None]:
    if not outputs or not normals:
        return None, None
    best_width = -1.0
    best_normal: Vec3 | None = None
    for normal in normals:
        width = min(abs(exact.dot(normal, output)) for output in outputs)
        if width > best_width:
            best_width = width
            best_normal = normal
    return best_width, best_normal


def quantile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[index]


def tangent_unit(c: Vec3, v: Vec3) -> Vec3 | None:
    projected = exact.project_onto_plane(c, v)
    if projected is None:
        return None
    return exact.normalize(projected)


def velocity_from_output_vorticity(c: Vec3, omega: Vec3) -> Vec3 | None:
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
        u_a = exact.normalize(velocity.u_a)
        u_b = exact.normalize(velocity.u_b)
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
    raise ValueError(f"unknown coherence channel: {name}")


def leakage_fraction(output: Vec3, channel: Vec3) -> float | None:
    channel_unit = exact.normalize(channel)
    if channel_unit is None:
        return None
    output_energy = exact.norm_sq(output)
    if output_energy <= EPS:
        return None
    coherent = exact.scale(exact.dot(output, channel_unit), channel_unit)
    leakage = exact.sub(output, coherent)
    return exact.norm_sq(leakage) / output_energy


def make_initial_state(
    rng: random.Random,
    rho_min: float,
    rho_max: float,
) -> CascadeState | None:
    frequency = random_frequency(rng, rho_min, rho_max)
    omega = random_vorticity_for_frequency(rng, frequency)
    if omega is None:
        return None
    return CascadeState(frequency=frequency, omega=omega)


def make_random_partner(
    rng: random.Random,
    rho_min: float,
    rho_max: float,
) -> CascadeState | None:
    return make_initial_state(rng, rho_min, rho_max)


def evaluate_triad(
    left: CascadeState,
    right: CascadeState,
    *,
    symmetrized: bool,
    coherence_channel: str,
) -> dict[str, Any] | None:
    bundle = exact.triadic_strain_eigenbundle(
        left.frequency,
        right.frequency,
        left.omega,
        right.omega,
        symmetrized=symmetrized,
    )
    if bundle is None:
        return None

    velocity = bundle.velocity
    strain = bundle.strain
    channel = channel_vector(coherence_channel, velocity, strain)
    if channel is None:
        return None
    leakage = leakage_fraction(velocity.u_c, channel)
    if leakage is None:
        return None

    c_hat = exact.normalize(velocity.c)
    if c_hat is None:
        return None
    sign_identity = exact.dot(velocity.a, strain.omega_out) + exact.dot(
        velocity.b,
        strain.omega_out,
    )
    relative_denominator = exact.norm(velocity.a) + exact.norm(velocity.b)
    relative_sign = (
        abs(sign_identity) / relative_denominator
        if relative_denominator > EPS
        else abs(sign_identity)
    )
    return {
        "bundle": bundle,
        "leakage": leakage,
        "sign_identity_abs": abs(sign_identity),
        "relative_sign_identity_abs": relative_sign,
        "output_divergence_abs": abs(exact.dot(c_hat, velocity.u_c)),
        "omega_c_dot_c_abs": abs(exact.dot(c_hat, strain.omega_out)),
        "output_direction": c_hat,
        "next_state": CascadeState(frequency=velocity.c, omega=strain.omega_out),
    }


def summarize_depth(
    depth: int,
    attempted: int,
    accepted: int,
    survivors: list[dict[str, Any]],
    all_leakages: list[float],
    sign_errors: list[float],
    relative_sign_errors: list[float],
    output_divergences: list[float],
    omega_c_dot_c_values: list[float],
    normals: list[Vec3],
) -> DepthStats:
    outputs = [row["output_direction"] for row in survivors]
    width, witness = estimate_width(outputs, normals)
    return DepthStats(
        depth=depth,
        attempted_triads=attempted,
        accepted_triads=accepted,
        survivors=len(survivors),
        survivor_fraction_of_accepted=(len(survivors) / accepted if accepted else None),
        output_width=width,
        output_width_witness=witness,
        min_leakage=quantile(all_leakages, 0.0),
        median_leakage=quantile(all_leakages, 0.5),
        p95_leakage=quantile(all_leakages, 0.95),
        max_leakage=quantile(all_leakages, 1.0),
        max_sign_identity_abs=max(sign_errors) if sign_errors else 0.0,
        mean_sign_identity_abs=(sum(sign_errors) / len(sign_errors) if sign_errors else None),
        max_relative_sign_identity_abs=max(relative_sign_errors) if relative_sign_errors else 0.0,
        max_output_divergence_abs=max(output_divergences) if output_divergences else 0.0,
        max_omega_c_dot_c_abs=max(omega_c_dot_c_values) if omega_c_dot_c_values else 0.0,
    )


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.depth <= 0:
        raise SystemExit("--depth must be positive")
    if args.continuations <= 0:
        raise SystemExit("--continuations must be positive")
    if args.max_paths_per_depth <= 0:
        raise SystemExit("--max-paths-per-depth must be positive")
    if args.zero_mode_threshold < 0.0:
        raise SystemExit("--zero-mode-threshold must be nonnegative")
    if args.rho_min <= 0.0 or args.rho_max <= 0.0 or args.rho_min > args.rho_max:
        raise SystemExit("--rho-min/--rho-max must be positive and ordered")

    rng = random.Random(args.seed)
    normals = fibonacci_sphere(args.normals)
    frontier: list[CascadeState] = []
    depth_stats: list[DepthStats] = []
    sample_survivors: list[SampleSurvivor] = []

    # Depth 1 starts from sampled left/right states.  Later depths use the
    # survivor output as the left state and sample fresh right partners.
    initial_left: list[CascadeState] = []
    for _ in range(args.samples):
        state = make_initial_state(rng, args.rho_min, args.rho_max)
        if state is not None:
            initial_left.append(state)

    for depth in range(1, args.depth + 1):
        attempted = 0
        accepted = 0
        survivors: list[dict[str, Any]] = []
        all_leakages: list[float] = []
        sign_errors: list[float] = []
        relative_sign_errors: list[float] = []
        output_divergences: list[float] = []
        omega_c_dot_c_values: list[float] = []

        if depth == 1:
            left_states = initial_left
            continuations = 1
        else:
            left_states = frontier
            continuations = args.continuations

        for left in left_states:
            for _ in range(continuations):
                if attempted >= args.max_paths_per_depth and depth > 1:
                    break
                right = make_random_partner(rng, args.rho_min, args.rho_max)
                if right is None:
                    continue
                if exact.norm(exact.add(left.frequency, right.frequency)) <= args.near_resonance_threshold:
                    continue
                attempted += 1
                row = evaluate_triad(
                    left,
                    right,
                    symmetrized=args.symmetrized,
                    coherence_channel=args.coherence_channel,
                )
                if row is None:
                    continue
                accepted += 1
                all_leakages.append(float(row["leakage"]))
                sign_errors.append(float(row["sign_identity_abs"]))
                relative_sign_errors.append(float(row["relative_sign_identity_abs"]))
                output_divergences.append(float(row["output_divergence_abs"]))
                omega_c_dot_c_values.append(float(row["omega_c_dot_c_abs"]))
                if row["leakage"] <= args.zero_mode_threshold:
                    survivors.append(row)
                    if len(sample_survivors) < args.sample_survivors:
                        sample_survivors.append(
                            SampleSurvivor(
                                depth=depth,
                                leakage_fraction=float(row["leakage"]),
                                sign_identity_abs=float(row["sign_identity_abs"]),
                                output_direction=row["output_direction"],
                            )
                        )
            if attempted >= args.max_paths_per_depth and depth > 1:
                break

        depth_stats.append(
            summarize_depth(
                depth,
                attempted,
                accepted,
                survivors,
                all_leakages,
                sign_errors,
                relative_sign_errors,
                output_divergences,
                omega_c_dot_c_values,
                normals,
            )
        )
        frontier = [row["next_state"] for row in survivors]
        if len(frontier) > args.max_paths_per_depth:
            rng.shuffle(frontier)
            frontier = frontier[: args.max_paths_per_depth]
        if not frontier:
            # Still return full stats for depths reached; no fabricated rows.
            break

    max_sign_error = max((row.max_sign_identity_abs for row in depth_stats), default=0.0)
    max_relative_sign_error = max(
        (row.max_relative_sign_identity_abs for row in depth_stats),
        default=0.0,
    )
    return {
        "contract": "ns_sign_antisymmetry_depth_sweep",
        "scope": "finite_exact_leray_vorticity_depth_sweep_diagnostic_only_not_pde_proof",
        "seed": args.seed,
        "parameters": {
            "samples": args.samples,
            "depth": args.depth,
            "continuations": args.continuations,
            "max_paths_per_depth": args.max_paths_per_depth,
            "rho_min": args.rho_min,
            "rho_max": args.rho_max,
            "zero_mode_threshold": args.zero_mode_threshold,
            "near_resonance_threshold": args.near_resonance_threshold,
            "symmetrized": args.symmetrized,
            "coherence_channel": args.coherence_channel,
            "normals": args.normals,
        },
        "depth_stats": [asdict(row) for row in depth_stats],
        "summary": {
            "depths_completed": len(depth_stats),
            "max_sign_antisymmetry_identity_abs": max_sign_error,
            "max_relative_sign_antisymmetry_identity_abs": max_relative_sign_error,
            "final_depth_survivors": depth_stats[-1].survivors if depth_stats else 0,
            "final_depth_output_width": depth_stats[-1].output_width if depth_stats else None,
            "sign_identity_pass_roundoff_1e-10": max_sign_error <= 1.0e-10,
            "survivor_counts_by_depth": [row.survivors for row in depth_stats],
            "output_width_by_depth": [row.output_width for row in depth_stats],
        },
        "sample_survivors": [asdict(row) for row in sample_survivors],
        "promotion": False,
        "clay_navier_stokes_promoted": False,
        "cascade_closed_zero_mode_output_width_proved": False,
        "pde_residual_sign_proved": False,
        "interpretation": (
            "The sign identity is finite algebra from c=a+b and omega_c tangent "
            "to c. Survivor counts/widths are thresholded diagnostics for the "
            "selected coherence channel, not a proof of cascade closure."
        ),
    }


def main() -> int:
    args = parse_args()
    report = run(args)
    text = json.dumps(report, indent=2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
