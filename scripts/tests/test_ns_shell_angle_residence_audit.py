from __future__ import annotations

from pathlib import Path
import sys

import numpy as np
import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_shell_angle_residence_audit import (  # noqa: E402
    audit,
    contiguous_residence,
    packet_geometry,
    IntervalRow,
)


def _groups(local_fraction: float = 0.9) -> list[dict[str, float | int]]:
    return [
        {"p_shell_offset": 0, "q_shell_offset": 0, "angle_bin": 4,
         "gross_activity": local_fraction},
        {"p_shell_offset": 3, "q_shell_offset": 0, "angle_bin": 8,
         "gross_activity": 1.0 - local_fraction},
    ]


def _state(path: Path, amplitude: float = 1.0) -> None:
    n = 8
    raw = np.zeros((n, n, n, 3), dtype=np.complex128)
    # target shell j=1 contains |k| in [2,4).  A conjugate pair gives positive
    # packet energy and dissipation without asserting a Navier--Stokes solution.
    raw[0, 0, 2, 1] = amplitude * (n ** 3)
    raw[0, 0, -2, 1] = amplitude * (n ** 3)
    np.savez(path, raw_hat=raw, nu=np.asarray(0.5), segment_window_c=np.asarray(0.1))


def test_packet_geometry_reports_explicit_tightness() -> None:
    geometry = packet_geometry(_groups(0.9), radius=1)
    assert geometry["local_shell_mass_fraction"] == pytest.approx(0.9)
    assert geometry["largest_group_mass_fraction"] == pytest.approx(0.9)
    assert geometry["effective_group_count"] > 1.0


def test_duration_weighted_contiguous_residence() -> None:
    rows = [
        IntervalRow("t", 0.0, 2.0, 0.1, 1.2, True),
        IntervalRow("t", 2.0, 3.0, 0.2, 1.1, True),
        IntervalRow("t", 5.0, 1.0, 0.1, 0.2, True),
        IntervalRow("t", 6.0, 4.0, 0.3, 2.0, False),
    ]
    result = contiguous_residence(rows, threshold=1.0)
    assert result["dangerous_duration"] == pytest.approx(5.0)
    assert result["longest_contiguous_dangerous_duration"] == pytest.approx(5.0)
    assert result["dangerous_parabolic_duration"] == pytest.approx(0.3)
    assert result["eligible_checkpoint_count"] == 3
    assert result["dangerous_checkpoint_count"] == 2


def test_end_to_end_audit_recomputes_full_packet_gamma(tmp_path: Path) -> None:
    state0 = tmp_path / "state0.npz"
    state1 = tmp_path / "state1.npz"
    _state(state0)
    _state(state1, amplitude=2.0)
    payload = {
        "trajectory_id": "synthetic",
        "export_receipts": [
            {
                "source_state": str(state0),
                "target_shell": 1,
                "full_packet_signed_rate": 1.0,
                "full_packet_gross_activity": 2.0,
                "coarse_shell_angle_groups": _groups(0.9),
            },
            {
                "source_state": str(state1),
                "target_shell": 1,
                "full_packet_signed_rate": -1.0,
                "full_packet_gross_activity": 3.0,
                "coarse_shell_angle_groups": _groups(0.95),
            },
        ],
    }
    result = audit(payload, (0.0, 1.0), radius=1, minimum_tightness=0.8,
                   duration_override=None, allow_missing_state=False)
    first, second = result["checkpoints"]
    assert first["gamma_available"] is True
    assert first["gamma"] > 0.0
    assert second["gamma"] == pytest.approx(0.0)
    assert first["duration"] == pytest.approx(0.05)  # c 2^-2j / nu
    assert first["parabolic_duration"] == pytest.approx(0.1)
    assert first["packet_tight"] is True
    assert result["authority"]["theorem_authority"] is False
    assert result["authority"]["bkm_authority"] is False
    assert result["authority"]["clay_authority"] is False
    assert result["trajectories"][0]["threshold_audits"][0]["eligible_checkpoint_count"] == 2


def test_missing_state_is_fail_closed_when_allowed(tmp_path: Path) -> None:
    payload = {
        "export_receipts": [{
            "source_state": str(tmp_path / "missing.npz"),
            "target_shell": 1,
            "full_packet_signed_rate": 1.0,
            "full_packet_gross_activity": 2.0,
            "coarse_shell_angle_groups": _groups(),
        }]
    }
    result = audit(payload, (1.0,), radius=1, minimum_tightness=0.8,
                   duration_override=None, allow_missing_state=True)
    row = result["checkpoints"][0]
    assert row["gamma_available"] is False
    assert row["gamma"] is None
    assert row["state_error"]
    threshold = result["trajectories"][0]["threshold_audits"][0]
    assert threshold["eligible_checkpoint_count"] == 0
    assert threshold["dangerous_duration_fraction"] is None
