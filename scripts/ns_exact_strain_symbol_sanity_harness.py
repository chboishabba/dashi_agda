#!/usr/bin/env python3
"""Sanity harness for the exact finite NS strain symbol.

This is a finite-dimensional diagnostic only.  It samples Fourier triads,
uses ``scripts/ns_exact_strain_eigenbundle.py`` for divergence-free input
vorticities, Biot-Savart velocities, the Leray-projected bilinear output, and
the induced strain eigenbundle, then checks the algebraic invariants directly.

The harness emits JSON and exits nonzero when an invariant error exceeds the
configured tolerance.  It proves no PDE sign estimate, no cascade width
theorem, and no Navier-Stokes regularity statement.
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
Mat3 = tuple[Vec3, Vec3, Vec3]
EPS = 1.0e-12


@dataclass(frozen=True)
class InvariantMaxima:
    input_omega_a_tangent_abs: float = 0.0
    input_omega_b_tangent_abs: float = 0.0
    input_u_a_tangent_abs: float = 0.0
    input_u_b_tangent_abs: float = 0.0
    output_velocity_tangent_abs: float = 0.0
    c_hat_u_hat_orthogonal_abs: float = 0.0
    omega_tangent_to_c_abs: float = 0.0
    omega_tangent_to_u_abs: float = 0.0
    frame_orthonormal_error: float = 0.0
    e_plus_residual: float = 0.0
    e_minus_residual: float = 0.0
    e_zero_residual: float = 0.0

    def max_error(self) -> float:
        return max(asdict(self).values())


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--tolerance", type=float, default=1.0e-10)
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit the full machine-readable report as JSON.",
    )
    return parser.parse_args()


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def strain_symbol(c_hat: Vec3, u_hat: Vec3) -> Mat3:
    return tuple(
        tuple(0.5 * (c_hat[i] * u_hat[j] + u_hat[i] * c_hat[j]) for j in range(3))
        for i in range(3)
    )  # type: ignore[return-value]


def mat_vec(matrix: Mat3, vector: Vec3) -> Vec3:
    return (
        exact.dot(matrix[0], vector),
        exact.dot(matrix[1], vector),
        exact.dot(matrix[2], vector),
    )


def residual(matrix: Mat3, vector: Vec3, eigenvalue: float) -> float:
    lhs = mat_vec(matrix, vector)
    rhs = exact.scale(eigenvalue, vector)
    return exact.norm(exact.sub(lhs, rhs))


def frame_orthonormal_error(e_plus: Vec3, e_minus: Vec3, e_zero: Vec3) -> float:
    frame = (e_plus, e_minus, e_zero)
    worst = 0.0
    for i, vi in enumerate(frame):
        for j, vj in enumerate(frame):
            target = 1.0 if i == j else 0.0
            worst = max(worst, abs(exact.dot(vi, vj) - target))
    return worst


def update_maxima(maxima: InvariantMaxima, values: dict[str, float]) -> InvariantMaxima:
    current = asdict(maxima)
    for key, value in values.items():
        current[key] = max(float(current[key]), abs(float(value)))
    return InvariantMaxima(**current)


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.tolerance <= 0.0:
        raise SystemExit("--tolerance must be positive")

    rng = random.Random(args.seed)
    maxima = InvariantMaxima()
    anti_parallel_rejects = 0
    degenerate_outputs = 0
    checked_rows = 0
    output_norms: list[float] = []

    models = ("e1", "e2", "plus45", "minus45", "angle")
    for index in range(args.samples):
        a = random_unit(rng)
        b = random_unit(rng)
        if exact.norm(exact.add(a, b)) <= EPS:
            anti_parallel_rejects += 1
            continue

        model_a = models[index % len(models)]
        model_b = models[(index + 2) % len(models)]
        bundle = exact.triadic_strain_eigenbundle_from_models(
            a,
            b,
            model_a=model_a,
            model_b=model_b,
            angle_a=rng.uniform(0.0, 2.0 * math.pi),
            angle_b=rng.uniform(0.0, 2.0 * math.pi),
        )
        if bundle is None:
            degenerate_outputs += 1
            continue

        velocity = bundle.velocity
        strain = bundle.strain
        output_norms.append(exact.norm(velocity.u_c))
        matrix = strain_symbol(strain.c_hat, strain.u_hat)

        maxima = update_maxima(
            maxima,
            {
                "input_omega_a_tangent_abs": exact.dot(velocity.a, velocity.omega_a),
                "input_omega_b_tangent_abs": exact.dot(velocity.b, velocity.omega_b),
                "input_u_a_tangent_abs": exact.dot(velocity.a, velocity.u_a),
                "input_u_b_tangent_abs": exact.dot(velocity.b, velocity.u_b),
                "output_velocity_tangent_abs": exact.dot(velocity.c, velocity.u_c),
                "c_hat_u_hat_orthogonal_abs": exact.dot(strain.c_hat, strain.u_hat),
                "omega_tangent_to_c_abs": exact.dot(strain.c_hat, strain.omega_out),
                "omega_tangent_to_u_abs": exact.dot(strain.u_hat, strain.omega_out),
                "frame_orthonormal_error": frame_orthonormal_error(
                    strain.e_plus,
                    strain.e_minus,
                    strain.e_zero,
                ),
                "e_plus_residual": residual(matrix, strain.e_plus, strain.lambda_plus),
                "e_minus_residual": residual(matrix, strain.e_minus, strain.lambda_minus),
                "e_zero_residual": residual(matrix, strain.e_zero, strain.lambda_zero),
            },
        )
        checked_rows += 1

    total_processed = args.samples - anti_parallel_rejects
    degeneracy_rate = (
        degenerate_outputs / total_processed if total_processed > 0 else float("nan")
    )
    max_error = maxima.max_error()
    pass_tolerance = max_error <= args.tolerance

    return {
        "contract": "ns_exact_strain_symbol_sanity_harness",
        "scope": "finite_exact_symbol_sanity_only_not_pde_proof",
        "dependency_policy": "pure_stdlib_plus_local_ns_exact_strain_eigenbundle_provider",
        "symbol_convention": "Biot-Savart inputs, Leray-projected bilinear output, S=1/2(c_hat_tensor_u_hat+u_hat_tensor_c_hat)",
        "seed": args.seed,
        "samples_requested": args.samples,
        "triads_processed": total_processed,
        "anti_parallel_rejects": anti_parallel_rejects,
        "checked_nonzero_output_rows": checked_rows,
        "degenerate_output_rows": degenerate_outputs,
        "degeneracy_rate": degeneracy_rate,
        "tolerance": args.tolerance,
        "max_invariant_errors": asdict(maxima),
        "max_invariant_error": max_error,
        "output_norm_min": min(output_norms) if output_norms else None,
        "output_norm_mean": (
            sum(output_norms) / len(output_norms) if output_norms else None
        ),
        "output_norm_max": max(output_norms) if output_norms else None,
        "invariants_pass": pass_tolerance,
        "clay_navier_stokes_promoted": False,
        "pde_residual_sign_proved": False,
    }


def main() -> int:
    args = parse_args()
    summary = run(args)
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        for key in (
            "contract",
            "samples_requested",
            "triads_processed",
            "checked_nonzero_output_rows",
            "degenerate_output_rows",
            "degeneracy_rate",
            "max_invariant_error",
            "invariants_pass",
        ):
            print(f"{key}: {summary[key]}")
    return 0 if summary["invariants_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
