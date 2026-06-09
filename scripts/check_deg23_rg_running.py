#!/usr/bin/env python3
"""One-loop QCD running diagnostic for the deg23 residual.

The receipt question is whether a one-loop running-mass factor can plausibly
explain the 14 -> 14.302 residual.  This script keeps the scale assumptions
explicit and does not promote Vcb, CKM, or physical adequacy.
"""

from __future__ import annotations

import json
import math


ALPHA_S_MZ = 0.118
MZ_GEV = 91.1876
NF = 5
NATURAL_DEG23 = 14.0
REQUIRED_DEG23 = 14.302


def beta0(nf: int) -> float:
    return 11.0 - 2.0 * nf / 3.0


def mass_exponent(nf: int) -> float:
    return 12.0 / (33.0 - 2.0 * nf)


def alpha_s_one_loop(mu_gev: float, nf: int = NF) -> float:
    b0 = beta0(nf)
    denom = 1.0 + ALPHA_S_MZ * b0 / (2.0 * math.pi) * math.log(mu_gev / MZ_GEV)
    return ALPHA_S_MZ / denom


def running_mass_factor(mu_low: float, mu_high: float, nf: int = NF) -> float:
    exponent = mass_exponent(nf)
    return (alpha_s_one_loop(mu_low, nf) / alpha_s_one_loop(mu_high, nf)) ** exponent


def solve_required_high_scale(mu_low: float, target_factor: float) -> float:
    lo = mu_low
    hi = mu_low * 4.0
    while running_mass_factor(mu_low, hi) < target_factor:
        hi *= 2.0
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        if running_mass_factor(mu_low, mid) < target_factor:
            lo = mid
        else:
            hi = mid
    return hi


def main() -> None:
    target_factor = REQUIRED_DEG23 / NATURAL_DEG23
    natural_scale_factor = running_mass_factor(5.0, 7.0)
    corrected_deg23 = NATURAL_DEG23 * natural_scale_factor
    required_high = solve_required_high_scale(5.0, target_factor)

    diagnostics = {
        "assumptions": {
            "alpha_s_MZ": ALPHA_S_MZ,
            "MZ_GeV": MZ_GEV,
            "nf": NF,
            "beta0": beta0(NF),
            "mass_exponent": mass_exponent(NF),
            "formula": "m(mu_low)/m(mu_high) = (alpha_s(mu_low)/alpha_s(mu_high))^(12/(33-2 nf))",
        },
        "target": {
            "natural_deg23": NATURAL_DEG23,
            "required_deg23": REQUIRED_DEG23,
            "target_factor": target_factor,
            "target_percent": 100.0 * (target_factor - 1.0),
        },
        "natural_p5_to_p7_scale_test": {
            "mu_low_GeV": 5.0,
            "mu_high_GeV": 7.0,
            "alpha_low": alpha_s_one_loop(5.0),
            "alpha_high": alpha_s_one_loop(7.0),
            "running_factor": natural_scale_factor,
            "running_percent": 100.0 * (natural_scale_factor - 1.0),
            "corrected_deg23": corrected_deg23,
            "signed_residual_after_correction": corrected_deg23 - REQUIRED_DEG23,
            "resolves_residual": False,
        },
        "tuned_scale_observation": {
            "mu_low_GeV": 5.0,
            "required_mu_high_GeV": required_high,
            "required_scale_ratio": required_high / 5.0,
            "factor_at_required_scale": running_mass_factor(5.0, required_high),
            "plausible_as_scale_choice_hypothesis": True,
            "closes_hypothesis": False,
        },
        "flags": {
            "rgRunningDiagnosticRecorded": True,
            "naturalP5P7RunningResolvesResidual": False,
            "rgRunningHypothesisClosed": False,
            "vcbPromotionClaimed": False,
            "physicalCKMPromoted": False,
        },
    }
    print(json.dumps(diagnostics, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
