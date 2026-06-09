#!/usr/bin/env python3
"""Finite-difference Jacobian harness for propagated NS coherence constraints.

This is a bounded local diagnostic only.  It samples exact finite
Leray-vorticity polarized cascade states using ``ns_exact_strain_eigenbundle``,
builds accumulated propagated-coherence constraint vectors

    K_1 = (old output zero-mode residual)
    K_k = K_1 plus propagated transition constraints through depth k,

and estimates finite-difference Jacobian ranks/singular values for ``dK_k``.

The harness is intended to falsify or stress-test candidate finite zero-mode
definitions.  It proves no PDE estimate, no output-width theorem, no
compensated leakage identity, and no Clay claim.  Promotion is always false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence

import numpy as np


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import ns_exact_strain_eigenbundle as exact_ns  # noqa: E402
import ns_propagated_polarization_coherence_harness as coherence  # noqa: E402


Vec3 = exact_ns.Vec3
EPS = 1.0e-12


@dataclass(frozen=True)
class DepthStats:
    depth: int
    valid_count: int
    invalid_count: int
    constraint_dimension: int
    parameter_dimension: int
    rank_distribution: dict[str, int]
    rank_mean: float | None
    rank_median: float | None
    min_singular_value_median: float | None
    max_singular_value_median: float | None
    condition_number_median: float | None
    residual_norm_median: float | None
    residual_norm_p90: float | None
    output_width: float | None
    output_count: int


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--samples", type=int, default=80)
    parser.add_argument("--max-depth", type=int, default=3)
    parser.add_argument("--normals", type=int, default=256)
    parser.add_argument("--finite-diff-step", type=float, default=1.0e-5)
    parser.add_argument("--rank-tol", type=float, default=1.0e-6)
    parser.add_argument("--near-resonance-threshold", type=float, default=1.0e-7)
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--show-samples", type=int, default=3)
    parser.add_argument("--json", action="store_true", help="Print JSON only.")
    return parser.parse_args(argv)


def clamp_depth(value: int) -> int:
    if value < 1:
        raise ValueError("--max-depth must be at least 1")
    if value > 5:
        raise ValueError("--max-depth is capped at 5 for bounded finite-difference cost")
    return value


def dot(u: Vec3, v: Vec3) -> float:
    return exact_ns.dot(u, v)


def norm(u: Vec3) -> float:
    return exact_ns.norm(u)


def normalize(u: Vec3) -> Vec3 | None:
    return exact_ns.normalize(u)


def scale(s: float, u: Vec3) -> Vec3:
    return exact_ns.scale(s, u)


def add(u: Vec3, v: Vec3) -> Vec3:
    return exact_ns.add(u, v)


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    phi = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(phi), r * math.sin(phi), z)


def unit_to_angles(v: Vec3) -> tuple[float, float]:
    v_hat = normalize(v)
    if v_hat is None:
        raise ValueError("cannot convert zero vector to spherical angles")
    theta = math.acos(max(-1.0, min(1.0, v_hat[2])))
    phi = math.atan2(v_hat[1], v_hat[0])
    return theta, phi


def angles_to_unit(theta: float, phi: float) -> Vec3:
    # Keep away from exact coordinate singularities after finite differences.
    theta = theta % (2.0 * math.pi)
    if theta > math.pi:
        theta = 2.0 * math.pi - theta
        phi += math.pi
    theta = min(math.pi - 1.0e-8, max(1.0e-8, theta))
    return (
        math.sin(theta) * math.cos(phi),
        math.sin(theta) * math.sin(phi),
        math.cos(theta),
    )


def angle_polarization(k: Vec3, angle: float) -> Vec3 | None:
    return exact_ns.vorticity_polarization(k, "angle", angle=angle)


def fibonacci_sphere(count: int) -> list[Vec3]:
    golden_angle = math.pi * (3.0 - math.sqrt(5.0))
    points: list[Vec3] = []
    for i in range(count):
        z = 1.0 - (2.0 * (i + 0.5) / count)
        r = math.sqrt(max(0.0, 1.0 - z * z))
        phi = golden_angle * i
        points.append((r * math.cos(phi), r * math.sin(phi), z))
    return points


def estimate_width(points: list[Vec3], normals: list[Vec3]) -> float | None:
    return coherence.estimate_width(points, normals)


def quantile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return float(ordered[index])


def median(values: list[float]) -> float | None:
    if not values:
        return None
    return float(statistics.median(values))


def finite_or_none(value: float) -> float | None:
    if math.isnan(value) or math.isinf(value):
        return None
    return float(value)


def vector_to_state(
    a: Vec3,
    b: Vec3,
    omega_a_angle: float,
    omega_b_angle: float,
    next_dirs: list[Vec3],
    next_omega_angles: list[float],
) -> np.ndarray:
    coords: list[float] = []
    for direction in (a, b):
        theta, phi = unit_to_angles(direction)
        coords.extend([theta, phi])
    coords.extend([omega_a_angle, omega_b_angle])
    for direction, angle in zip(next_dirs, next_omega_angles):
        theta, phi = unit_to_angles(direction)
        coords.extend([theta, phi, angle])
    return np.array(coords, dtype=float)


def decode_state(state: np.ndarray, max_depth: int) -> tuple[Vec3, Vec3, float, float, list[Vec3], list[float]]:
    if len(state) != 6 + 3 * (max_depth - 1):
        raise ValueError("state dimension does not match max depth")
    a = angles_to_unit(float(state[0]), float(state[1]))
    b = angles_to_unit(float(state[2]), float(state[3]))
    omega_a_angle = float(state[4])
    omega_b_angle = float(state[5])
    next_dirs: list[Vec3] = []
    next_omega_angles: list[float] = []
    cursor = 6
    for _ in range(max_depth - 1):
        next_dirs.append(angles_to_unit(float(state[cursor]), float(state[cursor + 1])))
        next_omega_angles.append(float(state[cursor + 2]))
        cursor += 3
    return a, b, omega_a_angle, omega_b_angle, next_dirs, next_omega_angles


def sample_state(rng: random.Random, max_depth: int, near_threshold: float) -> np.ndarray | None:
    for _ in range(256):
        a = random_unit(rng)
        b = random_unit(rng)
        if norm(add(a, b)) <= near_threshold:
            continue
        next_dirs = [random_unit(rng) for _ in range(max_depth - 1)]
        omega_angles = [rng.uniform(0.0, 2.0 * math.pi) for _ in range(max_depth + 1)]
        return vector_to_state(
            a,
            b,
            omega_angles[0],
            omega_angles[1],
            next_dirs,
            omega_angles[2:],
        )
    return None


def cascade_bundles(
    state: np.ndarray,
    depth: int,
    max_depth: int,
    near_threshold: float,
) -> list[exact_ns.TriadicStrainEigenbundle] | None:
    a, b, omega_a_angle, omega_b_angle, next_dirs, next_omega_angles = decode_state(state, max_depth)
    if norm(add(a, b)) <= near_threshold:
        return None
    omega_a = angle_polarization(a, omega_a_angle)
    omega_b = angle_polarization(b, omega_b_angle)
    if omega_a is None or omega_b is None:
        return None
    first = exact_ns.triadic_strain_eigenbundle(a, b, omega_a, omega_b)
    if first is None:
        return None

    bundles = [first]
    previous = first
    for step in range(1, depth):
        d = next_dirs[step - 1]
        if norm(add(previous.strain.c_hat, d)) <= near_threshold:
            return None
        omega_d = angle_polarization(d, next_omega_angles[step - 1])
        if omega_d is None:
            return None
        nxt = exact_ns.triadic_strain_eigenbundle(previous.strain.c_hat, d, previous.strain.omega_out, omega_d)
        if nxt is None:
            return None
        bundles.append(nxt)
        previous = nxt
    return bundles


def constraint_vector(
    state: np.ndarray,
    depth: int,
    max_depth: int,
    near_threshold: float,
) -> np.ndarray | None:
    bundles = cascade_bundles(state, depth, max_depth, near_threshold)
    if bundles is None:
        return None
    first = bundles[0]
    values = [
        coherence.family_output_zero_residual(
            first.strain.c_hat,
            first.velocity.a,
            first.velocity.b,
            first.strain.omega_out,
        )
    ]
    for previous, current in zip(bundles, bundles[1:]):
        record = coherence.build_record(previous, current)
        values.extend(
            [
                record.input_admissibility,
                record.second_output_zero_mode,
                record.omega_transport,
                record.velocity_transport,
                record.strain_plus_transport,
                record.carry_velocity,
            ]
        )
    return np.array(values, dtype=float)


def output_at_depth(
    state: np.ndarray,
    depth: int,
    max_depth: int,
    near_threshold: float,
) -> Vec3 | None:
    bundles = cascade_bundles(state, depth, max_depth, near_threshold)
    if bundles is None:
        return None
    return bundles[-1].strain.c_hat


def finite_difference_jacobian(
    state: np.ndarray,
    depth: int,
    max_depth: int,
    step: float,
    near_threshold: float,
) -> np.ndarray | None:
    base = constraint_vector(state, depth, max_depth, near_threshold)
    if base is None:
        return None
    rows = len(base)
    cols = len(state)
    jac = np.zeros((rows, cols), dtype=float)
    for col in range(cols):
        delta = np.zeros(cols, dtype=float)
        delta[col] = step
        plus = constraint_vector(state + delta, depth, max_depth, near_threshold)
        minus = constraint_vector(state - delta, depth, max_depth, near_threshold)
        if plus is None or minus is None:
            return None
        jac[:, col] = (plus - minus) / (2.0 * step)
    return jac


def rank_from_singular_values(singular_values: np.ndarray, tol: float) -> int:
    if singular_values.size == 0:
        return 0
    scale_ref = max(1.0, float(singular_values[0]))
    return int(sum(1 for value in singular_values if value > tol * scale_ref))


def summarize_depth(
    depth: int,
    valid: list[dict[str, Any]],
    invalid_count: int,
    parameter_dimension: int,
    normals: list[Vec3],
    outputs: list[Vec3],
) -> DepthStats:
    ranks = [int(row["rank"]) for row in valid]
    rank_distribution = {str(rank): ranks.count(rank) for rank in sorted(set(ranks))}
    min_singular = [row["singular_values"][-1] for row in valid if row["singular_values"]]
    max_singular = [row["singular_values"][0] for row in valid if row["singular_values"]]
    conditions = [
        row["condition_number"]
        for row in valid
        if row["condition_number"] is not None
    ]
    residual_norms = [row["residual_norm"] for row in valid]
    constraint_dimension = 1 + 6 * (depth - 1)
    return DepthStats(
        depth=depth,
        valid_count=len(valid),
        invalid_count=invalid_count,
        constraint_dimension=constraint_dimension,
        parameter_dimension=parameter_dimension,
        rank_distribution=rank_distribution,
        rank_mean=(sum(ranks) / len(ranks) if ranks else None),
        rank_median=median([float(rank) for rank in ranks]),
        min_singular_value_median=median([float(value) for value in min_singular]),
        max_singular_value_median=median([float(value) for value in max_singular]),
        condition_number_median=median([float(value) for value in conditions]),
        residual_norm_median=median([float(value) for value in residual_norms]),
        residual_norm_p90=quantile([float(value) for value in residual_norms], 0.90),
        output_width=estimate_width(outputs, normals),
        output_count=len(outputs),
    )


def rounded(value: float | None, digits: int = 8) -> float | None:
    if value is None:
        return None
    return round(float(value), digits)


def run(args: argparse.Namespace) -> dict[str, Any]:
    max_depth = clamp_depth(args.max_depth)
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.finite_diff_step <= 0.0:
        raise ValueError("--finite-diff-step must be positive")
    if args.rank_tol <= 0.0:
        raise ValueError("--rank-tol must be positive")

    rng = random.Random(args.seed)
    normals = fibonacci_sphere(args.normals)
    parameter_dimension = 6 + 3 * (max_depth - 1)

    states: list[np.ndarray] = []
    state_failures = 0
    for _ in range(args.samples):
        state = sample_state(rng, max_depth, args.near_resonance_threshold)
        if state is None:
            state_failures += 1
            continue
        states.append(state)

    depth_rows: dict[int, list[dict[str, Any]]] = {depth: [] for depth in range(1, max_depth + 1)}
    depth_invalid: dict[int, int] = {depth: 0 for depth in range(1, max_depth + 1)}
    depth_outputs: dict[int, list[Vec3]] = {depth: [] for depth in range(1, max_depth + 1)}

    for state in states:
        for depth in range(1, max_depth + 1):
            constraints = constraint_vector(
                state,
                depth,
                max_depth,
                args.near_resonance_threshold,
            )
            output = output_at_depth(
                state,
                depth,
                max_depth,
                args.near_resonance_threshold,
            )
            jac = finite_difference_jacobian(
                state,
                depth,
                max_depth,
                args.finite_diff_step,
                args.near_resonance_threshold,
            )
            if constraints is None or output is None or jac is None:
                depth_invalid[depth] += 1
                continue
            singular_values = np.linalg.svd(jac, compute_uv=False)
            rank = rank_from_singular_values(singular_values, args.rank_tol)
            smallest = float(singular_values[-1]) if singular_values.size else 0.0
            largest = float(singular_values[0]) if singular_values.size else 0.0
            condition = None if smallest <= EPS else largest / smallest
            depth_rows[depth].append(
                {
                    "rank": rank,
                    "singular_values": [float(x) for x in singular_values],
                    "condition_number": finite_or_none(condition) if condition is not None else None,
                    "residual_norm": float(np.linalg.norm(constraints)),
                }
            )
            depth_outputs[depth].append(output)

    depth_stats = [
        summarize_depth(
            depth,
            depth_rows[depth],
            depth_invalid[depth],
            parameter_dimension,
            normals,
            depth_outputs[depth],
        )
        for depth in range(1, max_depth + 1)
    ]

    sample_rows: list[dict[str, Any]] = []
    for index, state in enumerate(states[: args.show_samples]):
        row: dict[str, Any] = {"index": index}
        for depth in range(1, max_depth + 1):
            constraints = constraint_vector(state, depth, max_depth, args.near_resonance_threshold)
            row[f"depth_{depth}"] = {
                "constraint_norm": (
                    None if constraints is None else float(np.linalg.norm(constraints))
                ),
                "constraint_dimension": 1 + 6 * (depth - 1),
            }
        sample_rows.append(row)

    return {
        "contract": "ns_propagated_coherence_jacobian_harness",
        "scope": "finite_exact_leray_vorticity_jacobian_diagnostic_only_not_pde_proof",
        "promotion": False,
        "clay_navier_stokes_promoted": False,
        "output_width_theorem_proved": False,
        "compensated_leakage_identity_proved": False,
        "seed": args.seed,
        "parameters": {
            "samples": args.samples,
            "max_depth": max_depth,
            "normals": args.normals,
            "finite_diff_step": args.finite_diff_step,
            "rank_tol": args.rank_tol,
            "near_resonance_threshold": args.near_resonance_threshold,
            "parameter_dimension": parameter_dimension,
        },
        "states": {
            "sampled": len(states),
            "state_failures": state_failures,
        },
        "depths": [asdict(stat) for stat in depth_stats],
        "sample_rows": sample_rows,
        "interpretation": (
            "Ranks and singular values estimate local codimension of the sampled "
            "propagated-coherence constraint map K_k. Nonzero rank is diagnostic "
            "evidence only; it is not a transversality theorem or PDE proof."
        ),
    }


def print_text(report: dict[str, Any]) -> None:
    print("NS propagated coherence Jacobian harness")
    print(f"  scope: {report['scope']}")
    print(f"  promotion: {report['promotion']}")
    print(f"  seed: {report['seed']}")
    print(f"  states_sampled: {report['states']['sampled']}")
    for depth in report["depths"]:
        print(
            "  depth {depth}: valid={valid_count} rank_dist={rank_distribution} "
            "sv_min_med={svmin} width={width}".format(
                depth=depth["depth"],
                valid_count=depth["valid_count"],
                rank_distribution=depth["rank_distribution"],
                svmin=rounded(depth["min_singular_value_median"]),
                width=rounded(depth["output_width"]),
            )
        )


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    report = run(args)
    text = json.dumps(report, indent=2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    if args.json:
        print(text)
    else:
        print_text(report)
        print(text)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
