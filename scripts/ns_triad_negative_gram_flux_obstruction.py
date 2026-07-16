#!/usr/bin/env python3
"""Stress-test the negative-Gram-only Stage-3 bridge.

This is a diagnostic, not a proof.  It constructs one exact integer triad and
deterministic divergence-free complex Fourier data, then evaluates the
symmetrised finite Fourier transfer into each output mode.  The example shows
why a bound of the form

    |Q(u; z)| <= C * <z, L_neg z>

cannot hold for the full weighted energy error: the selected output transfer
is positive, so its negative coefficient is zero, while the weighted triad
contribution is nonzero.  Any physical bridge must retain an independently
controlled flux term (or change the quadratic weight).

It also scans the same deterministic family for the stronger failure: the
current *one-output* absolute orbit coefficient can be arbitrarily small while
the three-mode transfer variation remains order one.  Thus replacing L_neg by
the current L_abs does not by itself supply the Young weight either.

Finally, it checks the scaling obstruction to a state-independent positive
edge weight W: modal transfers scale cubically in u, so their W-dual squared
norm scales like lambda^6 whereas viscous dissipation scales like lambda^2.
Consequently a global FluxRem_W <= theta * D_viscous estimate needs either a
state-dependent/coercivity-normalised W or an additional energy hierarchy.
"""

from __future__ import annotations

import numpy as np


P = np.array([1.0, 0.0, 0.0])
Q = np.array([0.0, 1.0, 0.0])
R = -(P + Q)
WEIGHTS = np.array([0.0, 1.0, 3.0])


def leray(k: np.ndarray, value: np.ndarray) -> np.ndarray:
    return value - k * np.dot(k, value) / np.dot(k, k)


def divergence_free(k: np.ndarray, generator: np.random.Generator) -> np.ndarray:
    raw = generator.normal(size=3) + 1j * generator.normal(size=3)
    return leray(k, raw)


def modal_transfer(
    output: np.ndarray,
    left_input: np.ndarray,
    right_input: np.ndarray,
    coefficient: dict[tuple[float, float, float], np.ndarray],
) -> float:
    """One finite NS convolution contribution, with both input orders combined."""
    left = coefficient[tuple(left_input)]
    right = coefficient[tuple(right_input)]
    nonlinear = 1j * (
        np.dot(right_input, left) * right
        + np.dot(left_input, right) * left
    )
    return float(-np.real(np.vdot(coefficient[tuple(output)], leray(output, nonlinear))))


def main() -> None:
    generator = np.random.default_rng(20260716)
    for trial in range(10_000):
        coefficient: dict[tuple[float, float, float], np.ndarray] = {}
        for mode in (P, Q, R):
            coefficient[tuple(mode)] = divergence_free(mode, generator)
            coefficient[tuple(-mode)] = np.conj(coefficient[tuple(mode)])

        transfers = np.array(
            [
                modal_transfer(P, -Q, -R, coefficient),
                modal_transfer(Q, -R, -P, coefficient),
                modal_transfer(R, -P, -Q, coefficient),
            ]
        )
        weighted_error = float(np.dot(WEIGHTS, transfers))
        selected_negative_weight = max(0.0, -transfers[2])
        if (
            abs(float(np.sum(transfers))) < 1e-12
            and transfers[2] > 0.2
            and selected_negative_weight == 0.0
            and abs(weighted_error) > 0.1
        ):
            break
    else:
        raise AssertionError("no deterministic obstruction witness found")

    print("NEGATIVE_GRAM_ONLY_FLUX_OBSTRUCTION")
    print(f"trial={trial}")
    print(f"triad={P.astype(int).tolist(), Q.astype(int).tolist(), R.astype(int).tolist()}")
    print(f"transfers={transfers.tolist()}")
    print(f"transfer_sum={float(np.sum(transfers)):.17g}")
    print(f"selected_m_negative={selected_negative_weight:.17g}")
    print(f"weights={WEIGHTS.tolist()}")
    print(f"weighted_error={weighted_error:.17g}")

    # The exact Gram coefficient uses a positive amplitude factor times the
    # absolute transfer into one distinguished output.  A full triad energy
    # estimate instead needs all three transfer differences.  Search a fixed
    # finite sample for a near-zero distinguished output with nonzero transfer
    # variation; this is the singularity a proposed eta = m_abs split must
    # overcome analytically.
    generator = np.random.default_rng(20260716)
    best: tuple[float, int, np.ndarray, float, float] | None = None
    for trial in range(10_000):
        coefficient = {}
        for mode in (P, Q, R):
            coefficient[tuple(mode)] = divergence_free(mode, generator)
            coefficient[tuple(-mode)] = np.conj(coefficient[tuple(mode)])
        transfers = np.array(
            [
                modal_transfer(P, -Q, -R, coefficient),
                modal_transfer(Q, -R, -P, coefficient),
                modal_transfer(R, -P, -Q, coefficient),
            ]
        )
        edge_variation = float(
            ((transfers[0] - transfers[1]) ** 2
             + (transfers[0] - transfers[2]) ** 2
             + (transfers[1] - transfers[2]) ** 2)
            / 3.0
        )
        amplitude_factor = float(
            np.linalg.norm(coefficient[tuple(P)])
            * np.linalg.norm(coefficient[tuple(Q)])
            * np.linalg.norm(coefficient[tuple(R)])
            / 3.0
        )
        one_output_absolute_weight = amplitude_factor * abs(transfers[2])
        ratio = edge_variation / one_output_absolute_weight
        candidate = (ratio, trial, transfers, edge_variation, one_output_absolute_weight)
        if best is None or candidate[0] > best[0]:
            best = candidate

    assert best is not None
    ratio, ratio_trial, ratio_transfers, edge_variation, one_output_absolute_weight = best
    assert ratio > 100_000.0
    print("ONE_OUTPUT_ABSOLUTE_WEIGHT_FLUX_SINGULARITY")
    print(f"trial={ratio_trial}")
    print(f"transfers={ratio_transfers.tolist()}")
    print(f"edge_transfer_variation={edge_variation:.17g}")
    print(f"one_output_absolute_weight={one_output_absolute_weight:.17g}")
    print(f"variation_to_weight_ratio={ratio:.17g}")

    # With W fixed independently of u, the dual transfer flux is quadratic in
    # the modal transfers, hence degree six in u.  The standard Fourier
    # viscous form is degree two.  One concrete nonzero state makes the
    # homogeneity obstruction visible without asserting it as a theorem about
    # every possible state-dependent coercive construction.
    coefficient = {}
    for mode in (P, Q, R):
        coefficient[tuple(mode)] = divergence_free(mode, generator)
        coefficient[tuple(-mode)] = np.conj(coefficient[tuple(mode)])
    transfers = np.array(
        [
            modal_transfer(P, -Q, -R, coefficient),
            modal_transfer(Q, -R, -P, coefficient),
            modal_transfer(R, -P, -Q, coefficient),
        ]
    )
    edge_flux_at_one = float(
        ((transfers[0] - transfers[1]) ** 2
         + (transfers[0] - transfers[2]) ** 2
         + (transfers[1] - transfers[2]) ** 2)
        / 3.0
    )
    viscous_at_one = float(
        sum(np.dot(mode, mode) * np.vdot(coefficient[tuple(mode)], coefficient[tuple(mode)]).real
            for mode in (P, Q, R))
    )
    if edge_flux_at_one <= 1e-12 or viscous_at_one <= 1e-12:
        raise AssertionError("unexpected zero scaling witness")
    scales = (1.0, 2.0, 4.0)
    ratios = [
        (scale ** 6 * edge_flux_at_one) / (scale ** 2 * viscous_at_one)
        for scale in scales
    ]
    assert np.isclose(ratios[1] / ratios[0], 16.0)
    assert np.isclose(ratios[2] / ratios[1], 16.0)
    print("FIXED_EDGE_WEIGHT_VISCOUS_ABSORPTION_SCALING_OBSTRUCTION")
    print(f"edge_flux_at_one={edge_flux_at_one:.17g}")
    print(f"viscous_at_one={viscous_at_one:.17g}")
    print(f"scales={list(scales)}")
    print(f"flux_to_viscous_ratios={ratios}")


if __name__ == "__main__":
    main()
