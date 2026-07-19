from __future__ import annotations

import math
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_compact_gamma_differential_modulus_audit import (
    evaluate_rows,
    fit_constants,
    rational_compact_second_from_variations,
)


def _resolved_row(gamma_value: float, log_value: float) -> dict:
    return {
        "profile_id": "p",
        "center_profile_id": "c",
        "cutoff": 16,
        "target_shell": 2,
        "parabolic_time": 0.0,
        "path_parameter": 0.5,
        "tangent_kind": "path",
        "differential": {
            "resolved": True,
            "abs_gamma_directional_derivative_per_unit_XK": gamma_value,
            "abs_log_escape_directional_derivative_per_unit_XK": log_value,
            "minimum_mechanism_sign_distance": 0.25,
        },
    }


def test_rational_compact_second_matches_scalar_finite_difference() -> None:
    q0 = 2.3
    s0 = 1.7
    q_l = 0.4
    q_r = -0.2
    q_lr = 0.13
    s_l = -0.15
    s_r = 0.3
    s_lr = -0.07

    exact = rational_compact_second_from_variations(
        q=q0,
        s=s0,
        q_left=q_l,
        q_right=q_r,
        q_second=q_lr,
        s_left=s_l,
        s_right=s_r,
        s_second=s_lr,
    )

    def b(a: float, b_: float) -> float:
        q = q0 + a * q_l + b_ * q_r + a * b_ * q_lr
        s = s0 + a * s_l + b_ * s_r + a * b_ * s_lr
        return q / (q + s)

    eps = 2.0e-5
    mixed = (
        b(eps, eps)
        - b(eps, -eps)
        - b(-eps, eps)
        + b(-eps, -eps)
    ) / (4.0 * eps * eps)
    assert math.isclose(exact, mixed, rel_tol=2.0e-6, abs_tol=2.0e-7)


def test_fit_and_holdout_differential_constants() -> None:
    calibration = [_resolved_row(2.0, 1.0), _resolved_row(1.5, 0.5)]
    fitted = fit_constants(calibration, slack=0.25)
    assert math.isclose(fitted["fitted_gamma_differential_constant"], 2.5)
    assert math.isclose(fitted["fitted_log_escape_differential_constant"], 1.25)

    heldout = [_resolved_row(2.4, 1.2)]
    result = evaluate_rows(
        heldout,
        gamma_constant=fitted["fitted_gamma_differential_constant"],
        log_constant=fitted["fitted_log_escape_differential_constant"],
    )
    assert result["sampled_differential_modulus_survives"] is True
    assert result["minimum_gamma_margin"] > 0.0
    assert result["minimum_log_escape_margin"] > 0.0


def test_unresolved_differential_fails_closed() -> None:
    row = _resolved_row(0.0, 0.0)
    row["differential"] = {
        "resolved": False,
        "reason": "mechanism-sign-collision",
    }
    fitted = fit_constants([row], slack=0.1)
    assert fitted["finite_candidate"] is False
    assert math.isinf(fitted["fitted_gamma_differential_constant"])
    result = evaluate_rows([row], gamma_constant=1.0, log_constant=1.0)
    assert result["unresolved_row_count"] == 1
    assert result["sampled_differential_modulus_survives"] is False
