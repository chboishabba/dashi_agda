from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_galerkin_coherence_core import frequency_grid, leray_project_hat  # noqa: E402
from ns_r406_physical_real_eval import (  # noqa: E402
    evaluate_r406,
    helical_project,
    output_fibre,
    projected_state,
)
from ns_r650_c2_physical_real_scan import _critical_currency  # noqa: E402


def _reality_closed_random_state(n: int, seed: int = 23) -> np.ndarray:
    rng = np.random.default_rng(seed)
    physical = rng.normal(size=(n, n, n, 3))
    raw = np.fft.fftn(physical, axes=(0, 1, 2))
    wave, norm_sq, _norm, dealias = frequency_grid(n)
    return leray_project_hat(raw * dealias[..., None], wave, norm_sq)


def test_output_fibre_matches_literal_cube_resonance_count() -> None:
    # For cutoff 1 and output (1,0,0):
    # p_x can be 0 or 1; p_y,p_z each have 3 choices.
    assert len(output_fibre(1, (1, 0, 0))) == 18

    # For output (1,1,1), each p coordinate can be 0 or 1.
    assert len(output_fibre(1, (1, 1, 1))) == 8


def test_physical_real_helical_projectors_sum_to_leray() -> None:
    mode = (1, 2, -1)
    value = np.asarray((1.0 + 2.0j, -0.5 + 0.3j, 2.0 - 1.0j))
    k = np.asarray(mode, dtype=np.float64)
    leray = value - k * (np.dot(k, value) / np.dot(k, k))
    reconstructed = (
        helical_project(mode, value, +1)
        + helical_project(mode, value, -1)
    )
    assert np.allclose(reconstructed, leray, rtol=1.0e-13, atol=1.0e-13)


def test_r406_direct_companion_has_expected_quintic_amplitude_degree() -> None:
    raw = _reality_closed_random_state(6, seed=29)
    base = evaluate_r406(
        raw,
        nu=0.01,
        formal_cutoff=1,
        max_pairs=100_000,
    )
    doubled = evaluate_r406(
        2.0 * raw,
        nu=0.01,
        formal_cutoff=1,
        max_pairs=100_000,
    )

    r0 = float(base["r406_weighted_remainder"])
    r1 = float(doubled["r406_weighted_remainder"])
    assert abs(r0) > 1.0e-18
    assert np.isclose(r1, 32.0 * r0, rtol=5.0e-10, atol=1.0e-14)


def test_r406_pair_guard_count_is_deterministic() -> None:
    raw = _reality_closed_random_state(6, seed=31)
    row = evaluate_r406(
        raw,
        nu=0.01,
        formal_cutoff=1,
        max_pairs=100_000,
    )
    assert row["predicted_pair_count"] == row["evaluated_pair_count"]
    assert int(row["evaluated_pair_count"]) > 0
    assert float(row["minimum_pair_rate"]) > 0.0


def test_c2_margin_capacity_is_exact_scalar_rearrangement() -> None:
    raw = _reality_closed_random_state(6, seed=37)
    nu = 0.01
    cutoff = 1

    currency = _critical_currency(raw, nu=nu, formal_cutoff=cutoff)
    r406 = evaluate_r406(
        raw,
        nu=nu,
        formal_cutoff=cutoff,
        max_pairs=100_000,
    )

    production = float(currency["production_rate_2W"])
    dissipation = float(currency["critical_dissipation_rate"])
    remainder = float(r406["r406_weighted_remainder"])
    assert dissipation > 0.0

    delta_capacity = 2.0 * nu + (remainder - production) / dissipation
    strict_surplus_at_capacity = production - (2.0 * nu - delta_capacity) * dissipation

    assert np.isclose(
        strict_surplus_at_capacity,
        remainder,
        rtol=2.0e-11,
        atol=2.0e-13,
    )


def test_projected_state_uses_requested_formal_cube() -> None:
    raw = _reality_closed_random_state(9, seed=41)
    retained, forcing, meta = projected_state(raw, formal_cutoff=1)
    wave, _norm_sq, _norm, _dealias = frequency_grid(9)
    outside = np.max(np.abs(wave), axis=-1) > 1.0
    assert np.max(np.abs(retained[outside])) <= 1.0e-12
    assert np.max(np.abs(forcing[outside])) <= 1.0e-12
    assert meta["formal_cutoff"] == 1


def test_pointwise_c2_strengthening_fails_for_one_sign_at_large_amplitude() -> None:
    raw = _reality_closed_random_state(6, seed=43)
    nu = 0.01
    cutoff = 1

    base_r406 = evaluate_r406(
        raw,
        nu=nu,
        formal_cutoff=cutoff,
        max_pairs=100_000,
    )
    r0 = float(base_r406["r406_weighted_remainder"])
    assert abs(r0) > 1.0e-18

    # R406 is degree five and odd under common real amplitude scaling.  Choose
    # the sign making the quintic remainder negative; then search increasing
    # amplitudes for a failure of the stronger instantaneous inequality
    #
    #   P' - 2 nu D' <= R406.
    #
    # This is a no-go only for the pointwise strengthening, not for the actual
    # time-integrated R650 C2 theorem.
    oriented = raw if r0 < 0.0 else -raw
    failed = False
    for amplitude in (1.0, 3.0, 10.0, 30.0, 100.0, 300.0, 1_000.0):
        state = amplitude * oriented
        currency = _critical_currency(state, nu=nu, formal_cutoff=cutoff)
        r406 = evaluate_r406(
            state,
            nu=nu,
            formal_cutoff=cutoff,
            max_pairs=100_000,
        )
        production = float(currency["production_rate_2W"])
        dissipation = float(currency["critical_dissipation_rate"])
        remainder = float(r406["r406_weighted_remainder"])
        strict_surplus_delta_zero = production - 2.0 * nu * dissipation
        if strict_surplus_delta_zero > remainder:
            failed = True
            break

    assert failed
