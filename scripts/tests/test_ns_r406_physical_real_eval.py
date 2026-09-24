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
from ns_r650_c2_physical_real_scan import (  # noqa: E402
    _critical_currency,
    _packet_layer_cake_split,
)


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


def test_r652_c1_r406_diagonal_coupling_numeric_residual() -> None:
    raw = _reality_closed_random_state(6, seed=47)
    row = evaluate_r406(
        raw,
        nu=0.01,
        formal_cutoff=1,
        max_pairs=100_000,
    )
    scale = max(
        1.0,
        abs(float(row["c1_instantaneous_four_forcing_full"])),
        abs(2.0 * float(row["r406_weighted_remainder"])),
        abs(4.0 * float(row["global_forcing_full_diagonal"])),
    )
    assert abs(float(row["offdiagonal_minus_twice_direct_companion"])) <= 1.0e-12 * scale
    assert abs(float(row["c1_r406_diagonal_coupling_residual"])) <= 1.0e-12 * scale


def test_c1_forcing_full_has_expected_quintic_amplitude_degree() -> None:
    raw = _reality_closed_random_state(6, seed=53)
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
    c0 = float(base["c1_instantaneous_four_forcing_full"])
    c1 = float(doubled["c1_instantaneous_four_forcing_full"])
    assert abs(c0) > 1.0e-18
    assert np.isclose(c1, 32.0 * c0, rtol=5.0e-10, atol=1.0e-14)


def test_c2_packet_layer_cake_collar_remote_split_is_exact() -> None:
    raw = _reality_closed_random_state(12, seed=59)
    split = _packet_layer_cake_split(raw, nu=0.01, formal_cutoff=2)

    scale = max(
        1.0,
        abs(float(split["physical_upper_layer_cake"])),
        abs(float(split["collar_layer_cake"])),
        abs(float(split["remote_layer_cake"])),
    )
    assert abs(float(split["upper_minus_collar_remote_layer_cake"])) <= 1.0e-12 * scale
    assert abs(float(split["abel_reconstruction_residual"])) <= 1.0e-12 * scale
    assert float(split["maximum_upper_split_residual"]) <= 1.0e-12 * scale


def test_c2_low_remote_spectral_cross_is_nonpositive_on_literal_split() -> None:
    raw = _reality_closed_random_state(12, seed=61)
    split = _packet_layer_cake_split(raw, nu=0.01, formal_cutoff=2)

    assert int(split["interface_count"]) > 0
    assert int(split["remote_spectral_cross_violation_count"]) == 0
    assert float(split["maximum_remote_spectral_cross"]) <= 1.0e-10


def test_c2_full_off_packet_cross_reduces_to_collar() -> None:
    raw = _reality_closed_random_state(12, seed=67)
    split = _packet_layer_cake_split(raw, nu=0.01, formal_cutoff=2)

    assert int(split["interface_count"]) > 0
    assert float(split["maximum_cross_split_residual"]) <= 1.0e-10
    assert int(split["remote_spectral_cross_violation_count"]) == 0
    assert int(split["full_cross_below_collar_violation_count"]) == 0

    for row in split["interfaces"]:
        scale = max(
            1.0,
            abs(float(row["full_low_complement_spectral_cross"])),
            abs(float(row["collar_spectral_cross"])),
            abs(float(row["remote_spectral_cross"])),
        )
        assert abs(float(row["cross_split_residual"])) <= 1.0e-12 * scale
        assert (
            float(row["full_low_complement_spectral_cross"])
            <= float(row["collar_spectral_cross"]) + 1.0e-12 * scale
        )


def test_c2_euclidean_collar_refinement_reduces_cross_to_bad_cap() -> None:
    raw = _reality_closed_random_state(12, seed=71)
    split = _packet_layer_cake_split(raw, nu=0.01, formal_cutoff=2)

    assert int(split["interface_count"]) > 0
    assert float(split["maximum_collar_refinement_residual"]) <= 1.0e-10
    assert int(split["good_collar_spectral_cross_violation_count"]) == 0
    assert int(split["full_cross_below_bad_collar_violation_count"]) == 0

    for row in split["interfaces"]:
        scale = max(
            1.0,
            abs(float(row["collar_spectral_cross"])),
            abs(float(row["bad_collar_spectral_cross"])),
            abs(float(row["good_collar_spectral_cross"])),
        )
        assert abs(float(row["collar_refinement_residual"])) <= 1.0e-12 * scale
        assert float(row["good_collar_spectral_cross"]) <= 1.0e-12 * scale
        assert (
            float(row["full_low_complement_spectral_cross"])
            <= float(row["bad_collar_spectral_cross"]) + 1.0e-12 * scale
        )


def test_c2_collar_flux_refinement_is_exact() -> None:
    raw = _reality_closed_random_state(12, seed=73)
    split = _packet_layer_cake_split(raw, nu=0.01, formal_cutoff=2)

    assert int(split["interface_count"]) > 0
    assert float(split["maximum_collar_flux_refinement_residual"]) <= 1.0e-10
    for row in split["interfaces"]:
        scale = max(
            1.0,
            abs(float(row["collar_flux"])),
            abs(float(row["bad_collar_flux"])),
            abs(float(row["good_collar_flux"])),
        )
        assert (
            abs(float(row["collar_flux_refinement_residual"]))
            <= 1.0e-12 * scale
        )


def test_c2_critical_energy_has_expected_quadratic_scaling() -> None:
    raw = _reality_closed_random_state(12, seed=79)
    nu = 0.01
    cutoff = 2

    base = _critical_currency(raw, nu=nu, formal_cutoff=cutoff)
    doubled = _critical_currency(2.0 * raw, nu=nu, formal_cutoff=cutoff)

    x0 = float(base["critical_energy_X"])
    x1 = float(doubled["critical_energy_X"])
    assert x0 > 0.0
    assert np.isclose(x1, 4.0 * x0, rtol=2.0e-12, atol=1.0e-12)


def test_r685_r687_rate_lift_and_dynamic_cancellation_mirrors() -> None:
    raw = _reality_closed_random_state(6, seed=83)
    row = evaluate_r406(
        raw,
        nu=0.01,
        formal_cutoff=1,
        max_pairs=100_000,
        include_output_rows=True,
    )

    global_scale = max(
        1.0,
        abs(float(row["global_rate_lifted_forcing_full"])),
        abs(8.0 * float(row["global_coherent_commutator_work"])),
    )
    assert abs(float(row["r687_global_rate_lift_residual"])) <= 1.0e-12 * global_scale

    assert row["output_rows"] is not None
    for output_row in row["output_rows"]:
        scale = max(
            1.0,
            abs(float(output_row["rate_lifted_forcing_full"])),
            abs(8.0 * float(output_row["coherent_commutator_work"])),
            abs(float(output_row["weighted_rate_work"])),
        )
        assert abs(float(output_row["r687_rate_lift_residual"])) <= 1.0e-12 * scale
        assert abs(float(output_row["r685_rate_kernel_residual"])) <= 1.0e-12 * scale


def test_r687_rate_lift_is_quintic_but_r665_kernel_is_quartic() -> None:
    raw = _reality_closed_random_state(6, seed=89)
    kwargs = dict(
        nu=0.01,
        formal_cutoff=1,
        max_pairs=100_000,
    )
    base = evaluate_r406(raw, **kwargs)
    doubled = evaluate_r406(2.0 * raw, **kwargs)

    lifted0 = float(base["global_rate_lifted_forcing_full"])
    lifted1 = float(doubled["global_rate_lifted_forcing_full"])
    comm0 = float(base["global_coherent_commutator_work"])
    comm1 = float(doubled["global_coherent_commutator_work"])
    kernel0 = float(base["global_weighted_rate_work"])
    kernel1 = float(doubled["global_weighted_rate_work"])

    assert abs(lifted0) > 1.0e-18
    assert abs(comm0) > 1.0e-18
    assert abs(kernel0) > 1.0e-18

    assert np.isclose(lifted1, 32.0 * lifted0, rtol=5.0e-10, atol=1.0e-14)
    assert np.isclose(comm1, 32.0 * comm0, rtol=5.0e-10, atol=1.0e-14)
    assert np.isclose(kernel1, 16.0 * kernel0, rtol=5.0e-10, atol=1.0e-14)
