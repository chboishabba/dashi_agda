#!/usr/bin/env python3
"""Numerical diagnostic for the deg23 Faltings-height correction route."""

from __future__ import annotations

import json
import math

import mpmath as mp


def main() -> None:
    mp.mp.dps = 30
    chars = {
        -3: [0, 1, -1],
        -7: [0, 1, 1, -1, 1, -1, -1],
    }

    def log_derivative_at_one(character: list[int]) -> mp.mpf:
        eps = mp.mpf("1e-6")
        value = mp.dirichlet(1, character)
        derivative = (
            mp.dirichlet(1 + eps, character)
            - mp.dirichlet(1 - eps, character)
        ) / (2 * eps)
        return derivative / value

    heights = {}
    ratios = {}
    for discriminant, character in chars.items():
        ratio = log_derivative_at_one(character)
        ratios[discriminant] = ratio
        heights[discriminant] = (
            -mp.mpf("0.5") * mp.log(abs(discriminant))
            + mp.mpf("0.5") * ratio
            - mp.mpf("0.5") * mp.log(2 * mp.pi)
        )

    delta_h = heights[-3] - heights[-7]
    exp_two_delta = mp.e ** (2 * delta_h)
    corrected_deg23 = 14 * exp_two_delta

    payload = {
        "normalisation": "h_F(D)=-(1/2)log|D|+(1/2)(L'/L)(1,chi_D)-(1/2)log(2*pi)",
        "log_derivative_ratios": {
            str(k): float(v) for k, v in ratios.items()
        },
        "heights": {str(k): float(v) for k, v in heights.items()},
        "delta_h": float(delta_h),
        "exp_2_delta_h": float(exp_two_delta),
        "natural_deg23": 14,
        "corrected_deg23": float(corrected_deg23),
        "required_deg23": 14.302,
        "resolves_residual": bool(math.isclose(float(corrected_deg23), 14.302, rel_tol=1e-3)),
        "promotion_flags": {
            "physical_vcb_promoted": False,
            "faltings_correction_resolves_deg23_residual": False,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

