#!/usr/bin/env python3
"""Check the S^2 Biot-Savart strain mean-square formula.

This finite diagnostic verifies the local angular formula

    E_{S^2}[lambda(c)^2] = 11/60

for the sprint S^2 Biot-Savart eigenbundle symbol.  It uses midpoint
quadrature in polar angle theta and azimuth phi, with optional Monte Carlo
sampling from the uniform surface measure on S^2.

This is a local finite-symbol check only.  It is not a PDE regularity proof
and carries no Clay promotion.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


TARGET = 11.0 / 60.0


@dataclass(frozen=True)
class QuadratureResult:
    theta_bins: int
    phi_bins: int
    value: float
    target: float
    absolute_error: float
    weight_sum: float
    max_lambda_sq: float
    min_lambda_sq: float


@dataclass(frozen=True)
class MonteCarloResult:
    samples: int
    seed: int
    value: float
    target: float
    absolute_error: float
    max_lambda_sq: float
    min_lambda_sq: float


def lambda_sq(theta: float, phi: float) -> float:
    """Return lambda(c)^2 from the sprint angular m11/m12 symbol."""

    sin_theta = math.sin(theta)
    cos_theta = math.cos(theta)
    m11 = 0.5 * (
        cos_theta * cos_theta
        - sin_theta * sin_theta * math.cos(2.0 * phi)
    )
    m12 = -0.5 * sin_theta * sin_theta * math.sin(2.0 * phi)
    return m11 * m11 + m12 * m12


def midpoint_quadrature(theta_bins: int, phi_bins: int) -> QuadratureResult:
    if theta_bins <= 0:
        raise ValueError("--theta must be positive")
    if phi_bins <= 0:
        raise ValueError("--phi must be positive")

    dtheta = math.pi / theta_bins
    dphi = 2.0 * math.pi / phi_bins
    total = 0.0
    weight_sum = 0.0
    min_lam = math.inf
    max_lam = -math.inf

    for i in range(theta_bins):
        theta = (i + 0.5) * dtheta
        sin_theta = math.sin(theta)
        weight_theta = sin_theta * dtheta * dphi
        for j in range(phi_bins):
            phi = (j + 0.5) * dphi
            lam_sq = lambda_sq(theta, phi)
            total += lam_sq * weight_theta
            weight_sum += weight_theta
            min_lam = min(min_lam, lam_sq)
            max_lam = max(max_lam, lam_sq)

    value = total / (4.0 * math.pi)
    return QuadratureResult(
        theta_bins=theta_bins,
        phi_bins=phi_bins,
        value=value,
        target=TARGET,
        absolute_error=abs(value - TARGET),
        weight_sum=weight_sum,
        max_lambda_sq=max_lam,
        min_lambda_sq=min_lam,
    )


def monte_carlo(samples: int, seed: int) -> MonteCarloResult | None:
    if samples <= 0:
        return None

    rng = random.Random(seed)
    total = 0.0
    min_lam = math.inf
    max_lam = -math.inf

    for _ in range(samples):
        z = rng.uniform(-1.0, 1.0)
        theta = math.acos(z)
        phi = rng.uniform(0.0, 2.0 * math.pi)
        lam_sq = lambda_sq(theta, phi)
        total += lam_sq
        min_lam = min(min_lam, lam_sq)
        max_lam = max(max_lam, lam_sq)

    value = total / samples
    return MonteCarloResult(
        samples=samples,
        seed=seed,
        value=value,
        target=TARGET,
        absolute_error=abs(value - TARGET),
        max_lambda_sq=max_lam,
        min_lambda_sq=min_lam,
    )


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    quadrature = midpoint_quadrature(args.theta, args.phi)
    mc = monte_carlo(args.samples, args.seed)
    return {
        "harness": "ns_strain_mean_square_formula_harness",
        "script": "scripts/ns_strain_mean_square_formula_harness.py",
        "theorem_label": "NS-F5",
        "theorem_name": "NSBiotSavartStrainMeanSquareExactFormula",
        "formula": "E_S2[lambda^2] = 11/60",
        "exact_constants": {
            "mean_lambda_squared": TARGET,
            "mean_lambda_squared_fraction": "11/60",
            "rms_lambda": math.sqrt(TARGET),
        },
        "target": TARGET,
        "quadrature": asdict(quadrature),
        "monte_carlo": asdict(mc) if mc is not None else None,
        "promotion_false": True,
        "clay_promotion": False,
        "notes": [
            "midpoint quadrature uses sin(theta) surface weight",
            "Monte Carlo samples z uniformly in [-1,1] and phi uniformly in [0,2pi)",
            "finite angular symbol check only; not a PDE proof",
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Verify E_{S2}[lambda^2]=11/60 for the S2 Biot-Savart strain symbol."
    )
    parser.add_argument("--theta", type=int, default=240, help="polar midpoint bins")
    parser.add_argument("--phi", type=int, default=480, help="azimuth midpoint bins")
    parser.add_argument("--samples", type=int, default=0, help="optional Monte Carlo samples")
    parser.add_argument("--seed", type=int, default=20260608, help="Monte Carlo RNG seed")
    parser.add_argument("--json", action="store_true", help="emit JSON")
    parser.add_argument("--json-output", type=Path, help="write compact JSON payload to this path")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = build_payload(args)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        with args.json_output.open("w", encoding="utf-8") as handle:
            json.dump(payload, handle, sort_keys=True, separators=(",", ":"))
            handle.write("\n")
    if args.json:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    else:
        quad = payload["quadrature"]
        print("NS S2 Biot-Savart strain mean-square formula harness")
        print(f"target: {TARGET:.16f} (11/60)")
        print(
            "quadrature: "
            f"theta={quad['theta_bins']} phi={quad['phi_bins']} "
            f"value={quad['value']:.16f} "
            f"abs_error={quad['absolute_error']:.6e}"
        )
        if payload["monte_carlo"] is not None:
            mc = payload["monte_carlo"]
            print(
                "monte_carlo: "
                f"samples={mc['samples']} seed={mc['seed']} "
                f"value={mc['value']:.16f} "
                f"abs_error={mc['absolute_error']:.6e}"
            )
        print("clay_promotion: false")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
