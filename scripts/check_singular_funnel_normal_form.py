#!/usr/bin/env python3
"""Independent finite-epsilon diagnostic for the Yanchuk et al. normal form.

This reproduces one selected cross-section of the public source model using a
standalone fixed-step RK4 integrator. It is deliberately a numerical receipt,
not an analytic proof of the full singular-basin theorem.

Source model:
  dx/dt  = x (mu - x^2)
  dmu/dt = eps (-mu + a + b x)

Selected source parameters from Normal_forms/Normal_form_figure.m:
  a = -1, b = 2.3, eps = 0.1.

At mu0 = 3.9 the quasistatic attracting positive branch predicts the upper
stable state because mu0 lies above the reduced unstable threshold. The full
finite-epsilon flow nevertheless has an extremely narrow lower-attractor
funnel near x = 0.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

A = -1.0
B = 2.3
EPS = 0.1
MU0 = 3.9
DT = 0.005
T_FINAL = 500.0

LOWER_WITNESS_X = 1.0e-11
UPPER_WITNESS_X = 1.0e-10


def vector_field(x: float, mu: float) -> tuple[float, float]:
    return (
        x * (mu - x * x),
        EPS * (-mu + A + B * x),
    )


def rk4(x0: float, mu0: float, dt: float = DT, t_final: float = T_FINAL) -> tuple[float, float]:
    x = float(x0)
    mu = float(mu0)
    steps = int(round(t_final / dt))
    for _ in range(steps):
        k1x, k1m = vector_field(x, mu)
        k2x, k2m = vector_field(x + 0.5 * dt * k1x, mu + 0.5 * dt * k1m)
        k3x, k3m = vector_field(x + 0.5 * dt * k2x, mu + 0.5 * dt * k2m)
        k4x, k4m = vector_field(x + dt * k3x, mu + dt * k3m)
        x += (dt / 6.0) * (k1x + 2.0 * k2x + 2.0 * k3x + k4x)
        mu += (dt / 6.0) * (k1m + 2.0 * k2m + 2.0 * k3m + k4m)
    return x, mu


def positive_branch_equilibria() -> tuple[float, float, float, float]:
    # On x = sqrt(mu), write y = sqrt(mu). Equilibria satisfy
    # y^2 - B*y - A = 0.
    disc = B * B + 4.0 * A
    if disc <= 0.0:
        raise RuntimeError("selected source parameters do not give two positive-branch equilibria")
    y_small = 0.5 * (B - math.sqrt(disc))
    y_large = 0.5 * (B + math.sqrt(disc))
    return y_small, y_small * y_small, y_large, y_large * y_large


def classify_endpoint(x: float, mu: float) -> str:
    y_small, mu_saddle, y_large, mu_upper = positive_branch_equilibria()
    del y_small, mu_saddle
    d_lower = math.hypot(x, mu - A)
    d_upper = math.hypot(x - y_large, mu - mu_upper)
    if d_lower < 1.0e-5:
        return "lower"
    if d_upper < 1.0e-3:
        return "upper"
    return "unresolved"


def reduced_prediction(mu0: float) -> str:
    _, mu_saddle, _, _ = positive_branch_equilibria()
    # On the attracting positive critical branch, the smaller positive
    # equilibrium is the reduced separatrix threshold.
    return "upper" if mu0 > mu_saddle else "lower"


def classify_initial_x(x0: float) -> tuple[str, tuple[float, float]]:
    endpoint = rk4(x0, MU0)
    return classify_endpoint(*endpoint), endpoint


def boundary_bracket(
    lo: Fraction, hi: Fraction, iterations: int = 16
) -> tuple[Fraction, Fraction]:
    lo_class, _ = classify_initial_x(float(lo))
    hi_class, _ = classify_initial_x(float(hi))
    if lo_class != "lower" or hi_class != "upper":
        raise RuntimeError(
            f"bad initial bracket: lo={lo_class}, hi={hi_class}; expected lower/upper"
        )
    for _ in range(iterations):
        mid = (lo + hi) / 2
        mid_class, _ = classify_initial_x(float(mid))
        if mid_class == "lower":
            lo = mid
        elif mid_class == "upper":
            hi = mid
        else:
            raise RuntimeError(f"unresolved endpoint at x0={float(mid):.17g}")
    return lo, hi


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    lower_class, lower_endpoint = classify_initial_x(LOWER_WITNESS_X)
    upper_class, upper_endpoint = classify_initial_x(UPPER_WITNESS_X)
    reduced = reduced_prediction(MU0)
    bracket_lo, bracket_hi = boundary_bracket(
        Fraction(44, 10**12),
        Fraction(45, 10**12),
    )

    if lower_class != "lower":
        raise SystemExit(f"selected narrow-funnel witness no longer reaches lower attractor: {lower_class}")
    if upper_class != "upper":
        raise SystemExit(f"comparison initial state no longer reaches upper attractor: {upper_class}")
    if reduced != "upper":
        raise SystemExit(f"quasistatic selected branch unexpectedly predicts {reduced}")

    _, mu_saddle, x_upper, mu_upper = positive_branch_equilibria()
    payload = {
        "diagnostic": "yanchuk_normal_form_selected_funnel_cross_section",
        "source": {
            "doi": "10.1103/jtkh-9lz5",
            "public_repository": "hassanalkhayuon/Singular_Funnels",
            "source_file": "Normal_forms/Normal_form_figure.m",
        },
        "parameters": {
            "a": A,
            "b": B,
            "epsilon": EPS,
            "mu0": MU0,
            "dt": DT,
            "t_final": T_FINAL,
        },
        "reduced_positive_branch": {
            "unstable_mu_threshold": mu_saddle,
            "upper_attractor": [x_upper, mu_upper],
            "prediction_at_mu0": reduced,
        },
        "full_finite_epsilon": {
            "narrow_witness": {
                "initial": [LOWER_WITNESS_X, MU0],
                "endpoint": list(lower_endpoint),
                "classification": lower_class,
            },
            "comparison": {
                "initial": [UPPER_WITNESS_X, MU0],
                "endpoint": list(upper_endpoint),
                "classification": upper_class,
            },
            "stable_manifold_cross_section_bracket": [float(bracket_lo), float(bracket_hi)],
            "stable_manifold_cross_section_exact": {
                "lower": {
                    "numerator": bracket_lo.numerator,
                    "denominator": bracket_lo.denominator,
                },
                "upper": {
                    "numerator": bracket_hi.numerator,
                    "denominator": bracket_hi.denominator,
                },
                "common_denominator": bracket_lo.denominator,
                "adjacent_grid_points": (
                    bracket_lo.denominator == bracket_hi.denominator
                    and bracket_hi.numerator == bracket_lo.numerator + 1
                ),
            },
        },
        "observed_selected_mismatch": lower_class != reduced,
        "resolution_receipt": {
            "selected_bracket_width_exact": {
                "numerator": (bracket_hi - bracket_lo).numerator,
                "denominator": (bracket_hi - bracket_lo).denominator,
            },
            "agda_owner": "DASHI.Physics.Dynamics.YanchukSelectedCrossSectionBracketExact",
        },
        "claims": {
            "analytic_basin_theorem_proved": False,
            "global_width_law_proved": False,
            "finite_selected_cross_section_reproduced": True,
            "reduced_prediction_disagrees_with_selected_full_witness": lower_class != reduced,
        },
    }

    encoded = json.dumps(payload, indent=2, sort_keys=True)
    print(encoded)
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
