from __future__ import annotations

import math
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_compact_gamma_retained_danger_modulus_audit import (
    add_log_escape_loss,
    evaluate_retained_candidate,
)


def test_log_escape_loss_is_one_sided() -> None:
    pairs = [
        {"center_escape": 4.0, "member_escape": 2.0},
        {"center_escape": 2.0, "member_escape": 4.0},
    ]
    result = add_log_escape_loss(pairs)
    assert math.isclose(result[0]["positive_log_escape_loss"], math.log(2.0))
    assert result[1]["positive_log_escape_loss"] == 0.0


def test_retained_candidate_preserves_positive_lower() -> None:
    pairs = [
        {
            "profile_id": "p",
            "center_profile_id": "c",
            "target_shell": 2,
            "triad_count": 4,
            "parabolic_time": 0.0,
            "distance": 0.25,
            "member_gamma": 0.7,
            "center_gamma": 0.6,
            "member_escape": 2.0,
            "center_escape": 4.0,
            "member_dangerous": True,
            "center_dangerous": True,
        }
    ]
    result = evaluate_retained_candidate(
        exponent=0.5,
        gamma_constant=0.2,
        log_escape_constant=2.0 * math.log(2.0),
        gamma_threshold=0.7,
        member_pairs=pairs,
    )
    assert math.isclose(result["candidate_member_lower"], 2.0)
    assert result["sampled_retained_danger_modulus_survives"] is True
