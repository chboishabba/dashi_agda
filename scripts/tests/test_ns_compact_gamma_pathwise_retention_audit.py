from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_compact_gamma_pathwise_retention_audit import (
    evaluate_paths,
    fit_path_constants,
)


def sample_path(gamma_slope: float, log_slope: float) -> dict:
    length = 0.5
    center_escape = 4.0
    member_escape = center_escape * math.exp(-log_slope * length)
    return {
        "profile_id": "p",
        "center_profile_id": "c",
        "target_shell": 2,
        "cutoff": 16,
        "parabolic_time": 0.0,
        "resolved": True,
        "arc_length": length,
        "chord_distance": length,
        "minimum_escape_supply": member_escape,
        "samples": [
            {"resolved": True, "gamma": 0.5, "escape_supply": center_escape},
            {
                "resolved": True,
                "gamma": 0.5 + gamma_slope * length,
                "escape_supply": member_escape,
            },
        ],
        "segments": [
            {
                "resolved": True,
                "segment_length": length,
                "positive_gamma_rise": gamma_slope * length,
                "positive_log_escape_loss": log_slope * length,
                "gamma_lipschitz_quotient": gamma_slope,
                "log_escape_lipschitz_quotient": log_slope,
            }
        ],
    }


def test_path_constant_fit_and_retention_composition() -> None:
    path = sample_path(2.0, 1.0)
    fitted = fit_path_constants([path], slack=0.1)
    assert math.isclose(fitted["fitted_gamma_lipschitz_constant"], 2.2)
    assert math.isclose(fitted["fitted_log_escape_lipschitz_constant"], 1.1)
    result = evaluate_paths(
        [path],
        gamma_constant=fitted["fitted_gamma_lipschitz_constant"],
        log_escape_constant=fitted["fitted_log_escape_lipschitz_constant"],
        gamma_threshold=0.5,
    )
    assert result["sampled_pathwise_modulus_survives"] is True
    assert result["candidate_member_lower"] > 0.0


def test_unresolved_path_fails_closed() -> None:
    path = sample_path(0.0, 0.0)
    path["resolved"] = False
    result = evaluate_paths(
        [path], gamma_constant=1.0, log_escape_constant=1.0, gamma_threshold=0.5
    )
    assert result["unresolved_path_count"] == 1
    assert result["sampled_pathwise_modulus_survives"] is False


def test_synthetic_arc_length_dominates_chord() -> None:
    points = [np.array([0.0, 0.0]), np.array([0.5, 0.5]), np.array([1.0, 0.0])]
    arc = sum(float(np.linalg.norm(right - left)) for left, right in zip(points, points[1:]))
    chord = float(np.linalg.norm(points[-1] - points[0]))
    assert arc >= chord
