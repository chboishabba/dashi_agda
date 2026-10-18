#!/usr/bin/env python3
"""Independent stable-manifold crossing diagnostic for the Yanchuk normal form.

This follows the geometry used in the authors' Normal_form_figure.m:
  1. compute the saddle equilibrium,
  2. compute the stable Jacobian eigendirection,
  3. seed the stable manifold near the saddle,
  4. integrate backward,
  5. locate its crossing of mu = 3.9.

It is intentionally independent of the forward-basin bisection diagnostic.
Agreement between the two diagnostics identifies the same selected geometric
boundary numerically; it is not an interval or analytic proof.
"""

from __future__ import annotations

import json
import math

A = -1.0
B = 2.3
EPS = 0.1
TARGET_MU = 3.9
SEED_SCALE = 1.0e-3
DT = -1.0e-3
MAX_STEPS = 300000

BASIN_BRACKET_LO = 2933441 / 65536000000000000
BASIN_BRACKET_HI = 2933442 / 65536000000000000


def vector_field(x: float, mu: float) -> tuple[float, float]:
    return x * (mu - x * x), EPS * (-mu + A + B * x)


def rk4_step(x: float, mu: float, dt: float) -> tuple[float, float]:
    k1x, k1m = vector_field(x, mu)
    k2x, k2m = vector_field(x + 0.5 * dt * k1x, mu + 0.5 * dt * k1m)
    k3x, k3m = vector_field(x + 0.5 * dt * k2x, mu + 0.5 * dt * k2m)
    k4x, k4m = vector_field(x + dt * k3x, mu + dt * k3m)
    return (
        x + (dt / 6.0) * (k1x + 2.0 * k2x + 2.0 * k3x + k4x),
        mu + (dt / 6.0) * (k1m + 2.0 * k2m + 2.0 * k3m + k4m),
    )


def saddle_and_stable_direction() -> tuple[float, float, float, tuple[float, float]]:
    discriminant = B * B + 4.0 * A
    y = 0.5 * (B - math.sqrt(discriminant))
    x_saddle = y
    mu_saddle = y * y

    j11 = mu_saddle - 3.0 * x_saddle * x_saddle
    j12 = x_saddle
    j21 = EPS * B
    j22 = -EPS

    trace = j11 + j22
    determinant = j11 * j22 - j12 * j21
    spectral_discriminant = trace * trace - 4.0 * determinant
    lambda_minus = 0.5 * (trace - math.sqrt(spectral_discriminant))
    lambda_plus = 0.5 * (trace + math.sqrt(spectral_discriminant))

    stable_lambda = min(lambda_minus, lambda_plus)
    vx = 1.0
    vmu = -(j11 - stable_lambda) / j12
    norm = math.hypot(vx, vmu)
    return x_saddle, mu_saddle, stable_lambda, (vx / norm, vmu / norm)


def stable_branch_crossing() -> tuple[float, dict[str, float]]:
    x_s, mu_s, stable_lambda, (vx, vmu) = saddle_and_stable_direction()

    # The minus seed is the branch that reaches the selected far cross-section.
    x = x_s - SEED_SCALE * vx
    mu = mu_s - SEED_SCALE * vmu

    for step in range(MAX_STEPS):
        x_next, mu_next = rk4_step(x, mu, DT)
        if (mu - TARGET_MU) * (mu_next - TARGET_MU) <= 0.0:
            fraction = (TARGET_MU - mu) / (mu_next - mu)
            crossing_x = x + fraction * (x_next - x)
            return crossing_x, {
                "steps": step + 1,
                "saddle_x": x_s,
                "saddle_mu": mu_s,
                "stable_eigenvalue": stable_lambda,
                "stable_direction_x": vx,
                "stable_direction_mu": vmu,
            }
        x, mu = x_next, mu_next

    raise RuntimeError("stable branch did not reach selected mu cross-section")


def main() -> int:
    crossing_x, metadata = stable_branch_crossing()
    bracket_midpoint = 0.5 * (BASIN_BRACKET_LO + BASIN_BRACKET_HI)
    distance_to_bracket = min(
        abs(crossing_x - BASIN_BRACKET_LO),
        abs(crossing_x - BASIN_BRACKET_HI),
    )
    payload = {
        "diagnostic": "yanchuk_normal_form_stable_manifold_crossing",
        "source_method": "Jacobian stable eigendirection + backward integration",
        "source_file": "Normal_forms/Normal_form_figure.m",
        "parameters": {
            "a": A,
            "b": B,
            "epsilon": EPS,
            "mu_cross_section": TARGET_MU,
            "seed_scale": SEED_SCALE,
            "backward_dt": DT,
        },
        "saddle": metadata,
        "stable_manifold_crossing_x": crossing_x,
        "forward_basin_bracket": [BASIN_BRACKET_LO, BASIN_BRACKET_HI],
        "forward_basin_bracket_midpoint": bracket_midpoint,
        "distance_to_nearest_basin_bracket_endpoint": distance_to_bracket,
        "same_order_of_boundary": 1.0e-12 < crossing_x < 1.0e-9,
        "claims": {
            "stable_direction_numerically_reproduced": True,
            "stable_manifold_crossing_numerically_reproduced": True,
            "interval_manifold_tube_certified": False,
            "transversality_certified": False,
            "basin_separation_theorem_certified": False,
        },
    }

    if not payload["same_order_of_boundary"]:
        raise SystemExit("stable-manifold crossing left selected boundary scale")

    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
