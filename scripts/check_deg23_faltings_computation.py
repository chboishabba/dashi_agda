#!/usr/bin/env python3
"""Numerical Faltings/Colmez diagnostic for the deg23 residual.

This computes the prompt formula

  h_F(D) = -1/2 log|D| + 1/2 L'(1,chi_D)/L(1,chi_D) - 1/2 log(2*pi)

for the quadratic characters D=-3 and D=-7 using mpmath's Dirichlet
L-function evaluator.  The output is diagnostic only; it is not a certified
interval computation.
"""

from __future__ import annotations

import json
import mpmath as mp


CHARACTERS = {
    -3: [0, 1, -1],
    -7: [0, 1, 1, -1, 1, -1, -1],
}


def l_value(discriminant: int) -> mp.mpf:
    return mp.dirichlet(1, CHARACTERS[discriminant])


def l_prime(discriminant: int) -> mp.mpf:
    return mp.diff(lambda s: mp.dirichlet(s, CHARACTERS[discriminant]), 1)


def faltings_height(discriminant: int) -> dict[str, mp.mpf]:
    l1 = l_value(discriminant)
    lp = l_prime(discriminant)
    ratio = lp / l1
    height = (
        -mp.mpf("0.5") * mp.log(abs(discriminant))
        + mp.mpf("0.5") * ratio
        - mp.mpf("0.5") * mp.log(2 * mp.pi)
    )
    return {"L1": l1, "Lprime1": lp, "Lprime_over_L": ratio, "hF": height}


def as_float_dict(values: dict[str, mp.mpf]) -> dict[str, float]:
    return {key: float(value) for key, value in values.items()}


def main() -> None:
    mp.mp.dps = 50
    h3 = faltings_height(-3)
    h7 = faltings_height(-7)
    delta = h7["hF"] - h3["hF"]
    correction = mp.e ** (2 * delta)
    corrected_deg23 = mp.mpf(14) * correction
    required = mp.mpf("14.302")
    reverse_correction = mp.e ** (-2 * delta)
    reverse_corrected_deg23 = mp.mpf(14) * reverse_correction

    result = {
        "formula": "h_F(D)=-1/2 log|D| + 1/2 L'(1,chi_D)/L(1,chi_D) - 1/2 log(2*pi)",
        "D=-3": as_float_dict(h3),
        "D=-7": as_float_dict(h7),
        "delta_h": float(delta),
        "exp_2_delta_h": float(correction),
        "deg23_after_exp_2_delta_h": float(corrected_deg23),
        "deg23_required": float(required),
        "residual_after_correction": float(corrected_deg23 - required),
        "reverse_exp_2_delta_h": float(reverse_correction),
        "reverse_deg23_after_exp_2_delta_h": float(reverse_corrected_deg23),
        "required_factor": float(required / 14),
        "required_delta_h": float(mp.log(required / 14) / 2),
        "flags": {
            "faltingsNumericalComputationRecorded": True,
            "faltingsCorrectionResolvesDeg23Residual": False,
            "physicalVcbPromoted": False,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
