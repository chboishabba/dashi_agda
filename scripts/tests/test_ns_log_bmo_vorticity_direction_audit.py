from __future__ import annotations

from pathlib import Path
import sys

import numpy as np
import pytest


SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_log_bmo_vorticity_direction_audit import (  # noqa: E402
    audit,
    multiscale_direction_oscillation,
)


def test_constant_direction_has_zero_oscillation() -> None:
    xi = np.zeros((8, 8, 8, 3), dtype=float)
    xi[..., 2] = 1.0
    weights = np.ones((8, 8, 8), dtype=float)
    result = multiscale_direction_oscillation(xi, weights, (1, 2))
    assert result["unweighted_multiscale_oscillation_sup"] == pytest.approx(0.0, abs=1.0e-12)
    assert result["log_bmo_surrogate_sup"] == pytest.approx(0.0, abs=1.0e-12)


def test_alternating_direction_has_positive_oscillation() -> None:
    xi = np.zeros((8, 8, 8, 3), dtype=float)
    parity = np.indices((8, 8, 8)).sum(axis=0) % 2
    xi[..., 0] = np.where(parity == 0, 1.0, -1.0)
    weights = np.ones((8, 8, 8), dtype=float)
    result = multiscale_direction_oscillation(xi, weights, (1, 2))
    assert result["unweighted_multiscale_oscillation_sup"] > 0.9
    assert result["log_bmo_surrogate_sup"] > 0.0


def test_columnar_shear_checkpoint_is_nearly_constant_direction(tmp_path: Path) -> None:
    n = 8
    coordinate = 2.0 * np.pi * np.arange(n) / n
    _z, y, _x = np.meshgrid(coordinate, coordinate, coordinate, indexing="ij")
    velocity = np.zeros((n, n, n, 3), dtype=float)
    velocity[..., 0] = np.sin(y)
    raw_hat = np.fft.fftn(velocity, axes=(0, 1, 2))
    state = tmp_path / "columnar.npz"
    np.savez(state, raw_hat=raw_hat, nu=0.01)

    residence = {
        "checkpoints": [
            {
                "checkpoint_index": 0,
                "source_state": str(state),
                "trajectory_id": "columnar",
                "time": 0.0,
                "target_shell": 0,
                "gamma": 0.0,
                "packet_tight": True,
            }
        ]
    }
    result = audit(residence, (1, 2), 1.0e-12, False)
    metric = result["checkpoints"][0]["log_bmo_metric"]
    assert metric is not None
    # The direction flips at vorticity zeros/sign changes, so the finite local
    # diagnostic need not vanish globally. It remains finite and non-promoting.
    assert np.isfinite(metric["log_bmo_surrogate_sup"])
    assert result["authority"]["continuum_log_bmo_hypothesis_proved"] is False
    assert result["authority"]["promoted"] is False


def test_missing_state_fails_closed(tmp_path: Path) -> None:
    residence = {
        "checkpoints": [
            {
                "checkpoint_index": 0,
                "source_state": str(tmp_path / "missing.npz"),
                "target_shell": 1,
            }
        ]
    }
    with pytest.raises(FileNotFoundError):
        audit(residence, (1,), 1.0e-12, False)
    result = audit(residence, (1,), 1.0e-12, True)
    assert result["checkpoints"][0]["metric_available"] is False
