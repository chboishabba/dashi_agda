from __future__ import annotations

import math
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_compact_gamma_common_u_net_audit import PacketParameters
from ns_compact_gamma_remainder_oscillation_audit import jitter_parameters, pointwise_violation_summary


def make_profile(excess: float) -> dict:
    theta = 0.25
    escape = 2.0
    return {
        "profile_id": "fixture",
        "rows": [{
            "parabolic_time": 0.0,
            "gamma": 0.8,
            "mechanism_accounting": {
                "escape_supply": escape,
                "replenishment": theta * escape + excess,
            },
        }],
    }


def test_parameter_jitter_is_deterministic_and_admissible() -> None:
    base = PacketParameters(4, 0.0, 2.5, 0.55)
    kwargs = {
        "seed": 2,
        "sample_index": 3,
        "phase_jitter": 0.8,
        "log_ratio_jitter": 0.5,
        "log_satellite_jitter": 0.35,
    }
    left = jitter_parameters(base, **kwargs)
    right = jitter_parameters(base, **kwargs)
    assert left == right
    assert left.phase_spread >= 0.0
    assert left.target_ratio > 0.0
    assert 0.1 <= left.satellite_fraction <= 1.0


def test_positive_excess_is_reported() -> None:
    result = pointwise_violation_summary([make_profile(0.3)], theta=0.25)
    assert result["violation_row_count"] == 1
    assert math.isclose(result["maximum_pointwise_excess"], 0.3)


def test_zero_excess_is_not_reported() -> None:
    result = pointwise_violation_summary([make_profile(0.0)], theta=0.25)
    assert result["violation_row_count"] == 0
    assert result["maximum_pointwise_excess"] == 0.0
