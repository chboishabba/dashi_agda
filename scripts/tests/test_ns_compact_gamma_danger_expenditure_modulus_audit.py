from __future__ import annotations

import math
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_compact_gamma_danger_expenditure_modulus_audit import (
    evaluate_candidate,
    fit_holder_constant,
    row_at_time,
)


def test_holder_constant_uses_declared_exponent() -> None:
    pairs = [
        {
            "profile_id": "p",
            "center_profile_id": "c",
            "parabolic_time": 0.0,
            "distance": 0.25,
            "positive_escape_loss": 0.5,
        }
    ]
    result = fit_holder_constant(
        pairs,
        exponent=0.5,
        field="positive_escape_loss",
        slack=0.0,
    )
    assert math.isclose(result["raw_constant"], 1.0)
    assert math.isclose(result["fitted_constant"], 1.0)


def test_buffered_candidate_transfers_danger_and_escape_lower() -> None:
    center = {
        "profile_id": "c",
        "target_shell": 2,
        "parameters": {"triad_count": 4},
        "rows": [
            {
                "parabolic_time": 0.0,
                "gamma": 0.6,
                "mechanism_accounting": {
                    "escape_supply": 3.0,
                    "replenishment": 0.0,
                },
            }
        ],
    }
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
            "positive_gamma_loss": 0.1,
            "member_escape": 2.6,
            "center_escape": 3.0,
            "positive_escape_loss": 0.4,
            "member_dangerous": True,
            "center_dangerous": True,
        }
    ]
    result = evaluate_candidate(
        exponent=0.5,
        gamma_constant=0.2,
        escape_constant=0.8,
        gamma_threshold=0.7,
        centers=[center],
        member_pairs=pairs,
    )
    assert math.isclose(result["gamma_allowance"], 0.1)
    assert math.isclose(result["escape_allowance"], 0.4)
    assert math.isclose(result["buffered_center_threshold"], 0.6)
    assert math.isclose(result["candidate_member_lower"], 2.6)
    assert result["sampled_buffered_danger_modulus_survives"] is True


def test_row_lookup_rejects_missing_time() -> None:
    profile = {"profile_id": "p", "rows": [{"parabolic_time": 0.0}]}
    try:
        row_at_time(profile, 1.0)
    except ValueError as error:
        assert "expected one row" in str(error)
    else:
        raise AssertionError("missing time was accepted")
