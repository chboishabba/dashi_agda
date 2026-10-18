from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_galerkin_coherence_core import frequency_grid, leray_project_hat  # noqa: E402
from ns_r650_quantitative_stress_scan import literal_shell_index, state_metrics  # noqa: E402


def _reality_closed_random_state(n: int, seed: int = 7) -> np.ndarray:
    rng = np.random.default_rng(seed)
    physical = rng.normal(size=(n, n, n, 3))
    raw = np.fft.fftn(physical, axes=(0, 1, 2))
    wave, norm_sq, _norm, dealias = frequency_grid(n)
    return leray_project_hat(raw * dealias[..., None], wave, norm_sq)


def test_literal_shell_index_uses_ceiling_log2_max_norm() -> None:
    wave, _norm_sq, _norm, _dealias = frequency_grid(24)
    shells = literal_shell_index(wave)

    def value(kx: int, ky: int, kz: int) -> int:
        return int(shells[kz % 24, ky % 24, kx % 24])

    assert value(0, 0, 0) == 0
    assert value(1, 0, 0) == 0
    assert value(2, 0, 0) == 1
    assert value(3, 0, 0) == 2
    assert value(4, 1, 0) == 2
    assert value(5, 4, 3) == 3
    assert value(-5, 1, 0) == 3


def test_abel_reconstruction_matches_direct_weighted_transfer() -> None:
    raw = _reality_closed_random_state(24, seed=11)
    metrics = state_metrics(raw, nu=0.01, delta=0.0)

    scale = max(1.0, abs(float(metrics["literal_weighted_transfer_W"])))
    assert float(metrics["abel_identity_absolute_residual"]) <= 1.0e-10 * scale
    # The conservative simplification W=layerCake additionally depends on the
    # numerical energy-cancellation residual being small.
    conservation = abs(float(metrics["literal_unweighted_nonlinear_transfer"]))
    conservative_residual = float(metrics["conservative_layer_cake_absolute_residual"])
    assert conservative_residual <= 16.0 * conservation + 1.0e-10 * scale


def test_common_amplitude_scaling_is_cubic_vs_quadratic() -> None:
    raw = _reality_closed_random_state(24, seed=13)
    base = state_metrics(raw, nu=0.01, delta=0.0)
    scaled = state_metrics(2.0 * raw, nu=0.01, delta=0.0)

    p0 = float(base["literal_critical_production_rate_2W"])
    p1 = float(scaled["literal_critical_production_rate_2W"])
    d0 = float(base["literal_critical_dissipation_rate"])
    d1 = float(scaled["literal_critical_dissipation_rate"])

    assert abs(p0) > 1.0e-14
    assert d0 > 0.0
    assert np.isclose(p1, 8.0 * p0, rtol=2.0e-10, atol=1.0e-12)
    assert np.isclose(d1, 4.0 * d0, rtol=2.0e-12, atol=1.0e-12)


def test_large_amplitude_can_kill_viscosity_only_positive_margin() -> None:
    raw = _reality_closed_random_state(24, seed=1)

    # Orient the state so weighted production is positive; u -> -u flips the
    # cubic production while leaving quadratic dissipation unchanged.
    base = state_metrics(raw, nu=0.01, delta=0.0)
    if float(base["literal_critical_production_rate_2W"]) < 0.0:
        raw = -raw

    capacity = None
    for scale in (1.0, 10.0, 100.0, 1_000.0, 10_000.0, 100_000.0):
        row = state_metrics(scale * raw, nu=0.01, delta=0.0)
        capacity = row["viscosity_only_margin_capacity"]
        if capacity is not None and float(capacity) <= 0.0:
            break

    assert capacity is not None
    assert float(capacity) <= 0.0
