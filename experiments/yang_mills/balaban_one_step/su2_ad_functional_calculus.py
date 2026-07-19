#!/usr/bin/env python3
"""SU(2)-specific closed functional calculus for ad(Y).

The formulas are evaluated stably at the removable singularity and checked
against the exact 3x3 cross-product representation.  Outputs are finite
computations used to discover scalar bounds for the Agda proof lane.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Callable

import numpy as np

from common import write_receipt


def ad_matrix(y: np.ndarray) -> np.ndarray:
    """Matrix of [Y,X]=2 Y cross X in the repository normalization."""
    x, yy, z = np.asarray(y, dtype=float)
    return 2.0 * np.array(
        [[0.0, -z, yy], [z, 0.0, -x], [-yy, x, 0.0]], dtype=float
    )


def _dexp_b(theta: float) -> float:
    if abs(theta) < 1e-4:
        t2 = theta * theta
        return 0.5 - t2 / 24.0 + t2 * t2 / 720.0 - t2**3 / 40320.0
    return (1.0 - math.cos(theta)) / (theta * theta)


def _dexp_c(theta: float) -> float:
    if abs(theta) < 1e-4:
        t2 = theta * theta
        return 1.0 / 6.0 - t2 / 120.0 + t2 * t2 / 5040.0 - t2**3 / 362880.0
    return (theta - math.sin(theta)) / (theta**3)


def _inverse_c(theta: float) -> float:
    if abs(theta) < 1e-4:
        t2 = theta * theta
        return 1.0 / 12.0 + t2 / 720.0 + t2 * t2 / 30240.0 + t2**3 / 1209600.0
    half = 0.5 * theta
    return (1.0 - half / math.tan(half)) / (theta * theta)


def reduced_operator(A: np.ndarray, a: float, b: float, c: float) -> np.ndarray:
    return a * np.eye(A.shape[0]) + b * A + c * (A @ A)


def dexp_matrix(y: np.ndarray) -> np.ndarray:
    radius = float(np.linalg.norm(y))
    theta = 2.0 * radius
    A = ad_matrix(y)
    return reduced_operator(A, 1.0, _dexp_b(theta), _dexp_c(theta))


def inverse_dexp_matrix(y: np.ndarray) -> np.ndarray:
    radius = float(np.linalg.norm(y))
    theta = 2.0 * radius
    A = ad_matrix(y)
    return reduced_operator(A, 1.0, -0.5, _inverse_c(theta))


def numerical_derivative_bound(fun: Callable[[float], float], radius: float, samples: int) -> float:
    grid = np.linspace(0.0, radius, samples)
    h = max(radius / (samples * 10.0), 1e-7)
    values = []
    for x in grid:
        left = max(0.0, x - h)
        right = min(radius, x + h)
        if right == left:
            values.append(0.0)
        else:
            values.append(abs((fun(right) - fun(left)) / (right - left)))
    # Conservative numerical padding; this remains a finite-computation receipt,
    # not an interval theorem.
    return float(max(values, default=0.0) * 1.05 + 1e-12)


def run(radius: float, samples: int, seed: int) -> dict:
    rng = np.random.default_rng(seed)
    worst_cubic = 0.0
    worst_left = 0.0
    worst_right = 0.0
    for _ in range(samples):
        y = rng.normal(size=3)
        y *= rng.uniform(0.0, radius) / max(np.linalg.norm(y), 1e-30)
        A = ad_matrix(y)
        cubic_target = -4.0 * float(y @ y) * A
        worst_cubic = max(worst_cubic, float(np.linalg.norm(A @ A @ A - cubic_target, ord=2)))
        D = dexp_matrix(y)
        Di = inverse_dexp_matrix(y)
        worst_left = max(worst_left, float(np.linalg.norm(Di @ D - np.eye(3), ord=2)))
        worst_right = max(worst_right, float(np.linalg.norm(D @ Di - np.eye(3), ord=2)))

    theta_radius = 2.0 * radius
    return {
        "claim_scope": "finite_sample_scalar_bound_search",
        "radius": radius,
        "samples": samples,
        "ad_cubic_residual_max": worst_cubic,
        "inverse_left_residual_max": worst_left,
        "inverse_right_residual_max": worst_right,
        "candidate_derivative_bounds": {
            "dexp_linear": numerical_derivative_bound(_dexp_b, theta_radius, max(samples, 64)),
            "dexp_quadratic": numerical_derivative_bound(_dexp_c, theta_radius, max(samples, 64)),
            "inverse_quadratic": numerical_derivative_bound(_inverse_c, theta_radius, max(samples, 64)),
        },
        "branch_safe_candidate": bool(theta_radius < 2.0 * math.pi),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=float, default=0.25)
    parser.add_argument("--samples", type=int, default=128)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--out", default="operator_analysis/su2_ad_functional_calculus.json")
    args = parser.parse_args()
    report = run(args.radius, args.samples, args.seed)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    write_receipt(args.out, {"operator": "su2_ad_functional_calculus", **report})
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
