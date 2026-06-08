#!/usr/bin/env python3
"""NS signed leakage obstruction harness.

This finite-symbol harness separates two facts that must not be conflated:

* classical incompressible skew-symmetry passes for a fixed divergence-free
  test vector in the last two trilinear slots;
* the propagated-leakage-weighted triad contribution has no pointwise sign.

It is a local diagnostic only.  It proves no Hardy-space cancellation, no
compensated leakage identity, no critical residual estimate, and no Clay
Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import ns_exact_strain_eigenbundle as exact_ns  # noqa: E402


Vec3 = exact_ns.Vec3
EPS = 1.0e-12


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--rho-min", type=float, default=0.6)
    parser.add_argument("--rho-max", type=float, default=1.6)
    parser.add_argument("--sign-tolerance", type=float, default=1.0e-12)
    parser.add_argument("--near-resonance-threshold", type=float, default=1.0e-8)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="cap the effective sample count at 1000 for 10s smoke runs",
    )
    parser.add_argument(
        "--json-output",
        type=Path,
        default=REPO_ROOT / "outputs" / "ns_signed_leakage_obstruction_harness.json",
    )
    parser.add_argument("--json", action="store_true", help="print only JSON")
    return parser.parse_args()


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def random_tangent(k: Vec3, rng: random.Random) -> Vec3 | None:
    basis = exact_ns.tangent_basis(k)
    if basis is None:
        return None
    theta = rng.uniform(0.0, 2.0 * math.pi)
    return exact_ns.normalize(
        exact_ns.add(
            exact_ns.scale(math.cos(theta), basis.e1),
            exact_ns.scale(math.sin(theta), basis.e2),
        )
    )


def tangent_test_vector(k: Vec3) -> Vec3 | None:
    basis = exact_ns.tangent_basis(k)
    if basis is None:
        return None
    return basis.e1


def tangent_projection_unit(k: Vec3, v: Vec3) -> Vec3 | None:
    projected = exact_ns.project_onto_plane(k, v)
    if projected is None:
        return None
    return exact_ns.normalize(projected)


def split_lambda(output: Vec3, channel: Vec3) -> float | None:
    channel_unit = exact_ns.normalize(channel)
    output_energy = exact_ns.norm_sq(output)
    if channel_unit is None or output_energy <= EPS:
        return None
    coherent = exact_ns.scale(exact_ns.dot(output, channel_unit), channel_unit)
    leakage = exact_ns.sub(output, coherent)
    return exact_ns.norm_sq(leakage) / output_energy


def trilinear_slot_skew_error(velocity: exact_ns.TriadVelocityOutput, test: Vec3) -> float:
    """Classical last-slot skew-symmetry at one Fourier triad.

    With c=a+b and test vector v tangent to c, the integrated plane-wave
    identity is

        (u_a . b)(u_b . v) + (u_a . (-c))(v . u_b) = 0,

    because u_a . c = u_a . (a+b) = u_a . b.
    """

    first = exact_ns.dot(velocity.u_a, velocity.b) * exact_ns.dot(velocity.u_b, test)
    swapped_last_slots = exact_ns.dot(velocity.u_a, exact_ns.scale(-1.0, velocity.c)) * exact_ns.dot(
        test, velocity.u_b
    )
    return abs(first + swapped_last_slots)


def signed_triad_contribution(velocity: exact_ns.TriadVelocityOutput, channel: Vec3) -> float:
    """Signed finite contribution tested against a propagated coherence channel."""

    channel_unit = exact_ns.normalize(channel)
    if channel_unit is None:
        raise ValueError("coherence channel is degenerate")
    return exact_ns.dot(velocity.u_c, channel_unit)


def sample_bundle(
    rng: random.Random,
    rho_min: float,
    rho_max: float,
    near_resonance_threshold: float,
) -> exact_ns.TriadicStrainEigenbundle | None:
    for _ in range(128):
        rho = rng.uniform(rho_min, rho_max)
        a = exact_ns.scale(rho, random_unit(rng))
        b = random_unit(rng)
        if exact_ns.norm(exact_ns.add(a, b)) <= near_resonance_threshold:
            continue
        omega_a = random_tangent(a, rng)
        omega_b = random_tangent(b, rng)
        if omega_a is None or omega_b is None:
            continue
        bundle = exact_ns.triadic_strain_eigenbundle(
            a,
            b,
            omega_a,
            omega_b,
            symmetrized=True,
        )
        if bundle is not None:
            return bundle
    return None


def quantile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    idx = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[idx]


def summarize_values(values: list[float]) -> dict[str, float | None]:
    if not values:
        return {
            "min": None,
            "mean": None,
            "median": None,
            "p95": None,
            "max": None,
        }
    return {
        "min": min(values),
        "mean": sum(values) / len(values),
        "median": quantile(values, 0.5),
        "p95": quantile(values, 0.95),
        "max": max(values),
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.rho_min <= 0.0 or args.rho_max <= 0.0 or args.rho_min > args.rho_max:
        raise SystemExit("--rho-min/--rho-max must be positive and ordered")
    if args.sign_tolerance < 0.0:
        raise SystemExit("--sign-tolerance must be nonnegative")

    rng = random.Random(args.seed)
    effective_samples = min(args.samples, 1000) if args.quick else args.samples
    skew_errors: list[float] = []
    lambdas: list[float] = []
    signed_terms: list[float] = []
    weighted_terms: list[float] = []
    degenerate_rows = 0
    channel_degenerate_rows = 0
    sign_tol = args.sign_tolerance

    for _ in range(effective_samples):
        bundle = sample_bundle(
            rng,
            args.rho_min,
            args.rho_max,
            args.near_resonance_threshold,
        )
        if bundle is None:
            degenerate_rows += 1
            continue

        velocity = bundle.velocity
        test = tangent_test_vector(velocity.c)
        propagated_channel = tangent_projection_unit(
            velocity.c,
            exact_ns.add(velocity.u_a, velocity.u_b),
        )
        if test is None or propagated_channel is None:
            channel_degenerate_rows += 1
            continue

        lam = split_lambda(velocity.u_c, propagated_channel)
        if lam is None:
            channel_degenerate_rows += 1
            continue

        signed_t = signed_triad_contribution(velocity, propagated_channel)
        weighted = lam * signed_t
        skew_errors.append(trilinear_slot_skew_error(velocity, test))
        lambdas.append(lam)
        signed_terms.append(signed_t)
        weighted_terms.append(weighted)

    usable = len(weighted_terms)
    if usable == 0:
        raise SystemExit("no usable triads sampled")

    negative_count = sum(1 for value in weighted_terms if value < -sign_tol)
    positive_count = sum(1 for value in weighted_terms if value > sign_tol)
    zero_count = usable - negative_count - positive_count
    nonpositive_count = sum(1 for value in weighted_terms if value <= sign_tol)
    nonnegative_count = sum(1 for value in weighted_terms if value >= -sign_tol)
    negative_fraction = negative_count / usable
    positive_fraction = positive_count / usable
    triad_level_signed_fraction = nonpositive_count / usable
    best_one_sided_fraction = max(nonpositive_count, nonnegative_count) / usable
    weighted_mean = sum(weighted_terms) / usable

    pointwise_sign_fails = positive_count > 0 and negative_count > 0
    skew_error_max = max(skew_errors)
    skew_error_mean = sum(skew_errors) / len(skew_errors)

    pointwise_sign_obstruction = {
        "positive_count": positive_count,
        "negative_count": negative_count,
        "zero_count": zero_count,
        "positive_fraction": positive_fraction,
        "negative_fraction": negative_fraction,
        "zero_fraction": zero_count / usable,
        "skew_error_max": skew_error_max,
        "skew_error_mean": skew_error_mean,
        "weighted_mean": weighted_mean,
        "takes_both_signs": pointwise_sign_fails,
        "pointwise_nonpositive_bound_fails": positive_count > 0,
        "pointwise_nonnegative_bound_fails": negative_count > 0,
    }
    promotion_flags = {
        "finite_symbol_diagnostic": True,
        "pde_promotion": False,
        "clay_navier_stokes_promotion": False,
        "triadic_compensated_leakage_identity_proved": False,
        "terminal_promotion": False,
    }

    return {
        "contract": "ns_signed_leakage_obstruction_harness",
        "scope": "finite_exact_leray_symbol_diagnostic_only_not_pde_proof",
        "seed": args.seed,
        "quick": args.quick,
        "parameters": {
            "samples_requested": args.samples,
            "samples_effective": effective_samples,
            "rho_min": args.rho_min,
            "rho_max": args.rho_max,
            "near_resonance_threshold": args.near_resonance_threshold,
            "sign_tolerance": args.sign_tolerance,
        },
        "rows": {
            "usable": usable,
            "degenerate": degenerate_rows,
            "channel_degenerate": channel_degenerate_rows,
        },
        "pointwise_sign_obstruction": pointwise_sign_obstruction,
        "metrics": {
            "skew_symmetry_error": skew_error_max,
            "skew_symmetry_error_max": skew_error_max,
            "skew_symmetry_error_mean": skew_error_mean,
            "triad_level_signed_fraction": triad_level_signed_fraction,
            "weighted_lambda_T_mean": weighted_mean,
            "weighted_mean": weighted_mean,
            "negative_fraction": negative_fraction,
            "positive_fraction": positive_fraction,
            "zero_fraction": zero_count / usable,
            "best_one_sided_fraction": best_one_sided_fraction,
            "lambda_summary": summarize_values(lambdas),
            "signed_T_summary": summarize_values(signed_terms),
            "weighted_lambda_T_summary": summarize_values(weighted_terms),
        },
        "classical_skew_symmetry_fixed_test_vector_passes": skew_error_max <= 1.0e-10,
        "triad_level_pointwise_signed_bound_fails": pointwise_sign_fails,
        "promotion_flags": promotion_flags,
        "promotion": False,
        "clay_navier_stokes_promoted": False,
        "triadic_compensated_leakage_identity_proved": False,
        "conclusion": (
            "Classical last-slot skew-symmetry is visible for a fixed "
            "divergence-free test vector, but leakage-weighted triad "
            "contributions take both signs.  A pointwise triad-level signed "
            "leakage bound fails; only a global cancellation or square-function "
            "mechanism could remain."
        ),
    }


def main() -> int:
    args = parse_args()
    report = run(args)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(report, indent=2, sort_keys=True)
    args.json_output.write_text(text + "\n", encoding="utf-8")
    if args.json:
        print(text)
    else:
        print(f"wrote {args.json_output}")
        print(
            "skew_symmetry_error={:.3e} negative_fraction={:.3f} "
            "positive_fraction={:.3f} promotion={}".format(
                report["metrics"]["skew_symmetry_error"],
                report["metrics"]["negative_fraction"],
                report["metrics"]["positive_fraction"],
                str(report["promotion"]).lower(),
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
