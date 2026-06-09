#!/usr/bin/env python3
"""Toy finite-triad harness for true-Leray leakage square bookkeeping.

This is an algebraic consistency check only.  It samples finitely many Fourier
triads, projects input polarizations onto their divergence-free planes, applies
the true Leray output projector at zeta = xi + eta, and splits each output into
a chosen stretching direction plus its orthogonal leakage component.

The checked identity is the finite-dimensional Plancherel-style decomposition

    sum |B_out|^2 = sum |Pi_str B_out|^2 + sum |(I-Pi_str) B_out|^2

and equivalently

    sum lambda_triad |B_out|^2 = sum |(I-Pi_str) B_out|^2.

It is not a PDE proof, not a sign proof for the local residual, and not a Clay
Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Any

import numpy as np


EPS = 1.0e-12


@dataclass(frozen=True)
class TriadRow:
    index: int
    xi_norm: float
    eta_norm: float
    zeta_norm: float
    input_xi_divergence_abs: float
    input_eta_divergence_abs: float
    output_divergence_abs: float
    stretching_divergence_abs: float
    output_energy: float
    stretching_energy: float
    leakage_energy: float
    lambda_leakage_fraction: float
    reconstruction_error: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--triads", type=int, default=256)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument(
        "--near-resonance-threshold",
        type=float,
        default=1.0e-6,
        help="Resample when |xi + eta| is below this threshold.",
    )
    return parser.parse_args()


def unit(v: np.ndarray) -> np.ndarray:
    norm = float(np.linalg.norm(v))
    if norm < EPS:
        raise ValueError("cannot normalize near-zero vector")
    return v / norm


def project_perp(direction: np.ndarray, vector: np.ndarray) -> np.ndarray:
    d = unit(direction)
    return vector - float(np.dot(vector, d)) * d


def random_nonzero_vector(rng: np.random.Generator) -> np.ndarray:
    while True:
        v = rng.normal(size=3)
        if np.linalg.norm(v) > EPS:
            return v


def random_divergence_free_vector(
    rng: np.random.Generator, frequency: np.ndarray
) -> np.ndarray:
    while True:
        raw = rng.normal(size=3)
        projected = project_perp(frequency, raw)
        norm = float(np.linalg.norm(projected))
        if norm > EPS:
            return projected / norm


def leray_project(frequency: np.ndarray, vector: np.ndarray) -> np.ndarray:
    return project_perp(frequency, vector)


def stretching_direction(frequency: np.ndarray) -> np.ndarray:
    """Choose a deterministic unit vector in the zeta-tangent plane.

    This is a toy stand-in for a strain/stretching eigenvector.  It deliberately
    depends only on the output direction and is always perpendicular to zeta.
    """

    zhat = unit(frequency)
    basis_candidates = (
        np.array([1.0, 0.0, 0.0]),
        np.array([0.0, 1.0, 0.0]),
        np.array([0.0, 0.0, 1.0]),
    )
    candidate = min(basis_candidates, key=lambda e: abs(float(np.dot(e, zhat))))
    return unit(project_perp(frequency, candidate))


def true_leray_unsym_bilinear_output(
    xi: np.ndarray,
    eta: np.ndarray,
    u_xi: np.ndarray,
    u_eta: np.ndarray,
) -> np.ndarray:
    """Apply the unsymmetrized true Leray NS bilinear symbol.

    Up to the harmless complex phase and magnitude conventions, the Fourier
    symbol is

        P(zeta) [ (eta . u_hat(xi)) u_hat(eta) ],

    with zeta = xi + eta.  This is sufficient for the finite leakage split
    identity checked by this harness.
    """

    zeta = xi + eta
    scalar = float(np.dot(eta, u_xi))
    raw = scalar * u_eta
    return leray_project(zeta, raw)


def make_triad_row(
    rng: np.random.Generator, index: int, threshold: float
) -> TriadRow:
    while True:
        xi = random_nonzero_vector(rng)
        eta = random_nonzero_vector(rng)
        zeta = xi + eta
        if np.linalg.norm(zeta) > threshold:
            break

    u_xi = random_divergence_free_vector(rng, xi)
    u_eta = random_divergence_free_vector(rng, eta)
    output = true_leray_unsym_bilinear_output(xi, eta, u_xi, u_eta)
    stretch_dir = stretching_direction(zeta)
    stretch = float(np.dot(output, stretch_dir)) * stretch_dir
    leakage = output - stretch

    output_energy = float(np.dot(output, output))
    stretching_energy = float(np.dot(stretch, stretch))
    leakage_energy = float(np.dot(leakage, leakage))
    lambda_fraction = leakage_energy / output_energy if output_energy > EPS else 0.0
    reconstruction_error = abs(output_energy - stretching_energy - leakage_energy)

    return TriadRow(
        index=index,
        xi_norm=float(np.linalg.norm(xi)),
        eta_norm=float(np.linalg.norm(eta)),
        zeta_norm=float(np.linalg.norm(zeta)),
        input_xi_divergence_abs=abs(float(np.dot(unit(xi), u_xi))),
        input_eta_divergence_abs=abs(float(np.dot(unit(eta), u_eta))),
        output_divergence_abs=abs(float(np.dot(unit(zeta), output))),
        stretching_divergence_abs=abs(float(np.dot(unit(zeta), stretch_dir))),
        output_energy=output_energy,
        stretching_energy=stretching_energy,
        leakage_energy=leakage_energy,
        lambda_leakage_fraction=lambda_fraction,
        reconstruction_error=reconstruction_error,
    )


def stable_summary(rows: list[TriadRow], seed: int) -> dict[str, Any]:
    output_sum = sum(row.output_energy for row in rows)
    stretch_sum = sum(row.stretching_energy for row in rows)
    leakage_sum = sum(row.leakage_energy for row in rows)
    lambda_weighted_sum = sum(
        row.lambda_leakage_fraction * row.output_energy for row in rows
    )
    identity_error = abs(output_sum - stretch_sum - leakage_sum)
    lambda_identity_error = abs(lambda_weighted_sum - leakage_sum)

    lambdas = np.array([row.lambda_leakage_fraction for row in rows], dtype=float)
    output_divs = np.array([row.output_divergence_abs for row in rows], dtype=float)
    input_divs = np.array(
        [
            max(row.input_xi_divergence_abs, row.input_eta_divergence_abs)
            for row in rows
        ],
        dtype=float,
    )

    return {
        "contract": "ns_leakage_square_toy_harness",
        "scope": "finite_triad_algebra_only_not_pde_proof",
        "seed": seed,
        "triad_count": len(rows),
        "output_energy_sum": output_sum,
        "stretching_energy_sum": stretch_sum,
        "leakage_energy_sum": leakage_sum,
        "lambda_weighted_output_energy_sum": lambda_weighted_sum,
        "orthogonal_split_identity_error": identity_error,
        "lambda_plancherel_identity_error": lambda_identity_error,
        "max_row_reconstruction_error": max(row.reconstruction_error for row in rows),
        "max_input_divergence_abs": float(np.max(input_divs)),
        "max_output_divergence_abs": float(np.max(output_divs)),
        "lambda_min": float(np.min(lambdas)),
        "lambda_mean": float(np.mean(lambdas)),
        "lambda_median": float(np.median(lambdas)),
        "lambda_max": float(np.max(lambdas)),
        "zero_output_rows": sum(row.output_energy <= EPS for row in rows),
        "identity_pass_tolerance": 1.0e-10,
        "orthogonal_split_identity_pass": identity_error <= 1.0e-10,
        "lambda_plancherel_identity_pass": lambda_identity_error <= 1.0e-10,
        "divergence_projection_pass": (
            float(np.max(input_divs)) <= 1.0e-10
            and float(np.max(output_divs)) <= 1.0e-10
        ),
        "clay_navier_stokes_promoted": False,
        "pde_residual_sign_proved": False,
        "triadic_compensated_leakage_identity_proved": False,
    }


def main() -> int:
    args = parse_args()
    if args.triads <= 0:
        raise SystemExit("--triads must be positive")
    rng = np.random.default_rng(args.seed)
    rows = [
        make_triad_row(rng, index, args.near_resonance_threshold)
        for index in range(args.triads)
    ]
    summary = stable_summary(rows, args.seed)
    payload = {
        "summary": summary,
        "sample_rows": [asdict(row) for row in rows[:5]],
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if all(
        [
            summary["orthogonal_split_identity_pass"],
            summary["lambda_plancherel_identity_pass"],
            summary["divergence_projection_pass"],
        ]
    ) else 1


if __name__ == "__main__":
    raise SystemExit(main())
