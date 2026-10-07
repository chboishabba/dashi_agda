#!/usr/bin/env python3
"""Executable benchmark for Schuetzhold controlled EM<->GW exchange.

Source benchmark (arXiv:2502.10221 / PRL 135, 171501):
  h ~ 1e-22, optical angular frequency Omega ~ 1e15 s^-1,
  pulse energy ~ mJ, GW angular frequency ~ 2*pi*kHz,
  phase accumulation time of a few seconds.

The benchmark also derives the ideal coherent-state delay requirement

    h * Omega * tau * sqrt(N) >= target_snr,

so a million-reflection delay is an example rather than a mathematical
requirement.  Optical survival is separately parameterized by per-reflection
loss.  This is not a complete apparatus noise model and does not claim an
experimental observation.
"""

from dataclasses import dataclass
from math import exp, log, pi, sqrt

HBAR = 1.054_571_817e-34  # J s, rounded numerical realization
C = 299_792_458.0  # m/s, exact SI value represented as float here


@dataclass(frozen=True)
class Benchmark:
    strain: float = 1.0e-22
    optical_omega: float = 1.0e15  # rad/s order-of-magnitude benchmark
    pulse_energy: float = 1.0e-3  # J
    gw_frequency_hz: float = 1.0e3
    delay_time: float = 3.0  # s
    target_snr: float = 1.0
    reflection_count: int = 1_000_000
    per_reflection_loss: float = 1.0e-6


def evaluate(b: Benchmark = Benchmark()) -> dict[str, float]:
    photon_energy = HBAR * b.optical_omega
    photon_count = b.pulse_energy / photon_energy

    single_arm_delta_omega = 0.5 * b.strain * b.optical_omega
    differential_delta_omega = 2.0 * single_arm_delta_omega
    relative_phase = differential_delta_omega * b.delay_time

    half_cycle_delta_energy = 0.5 * b.strain * b.pulse_energy
    gw_omega = 2.0 * pi * b.gw_frequency_hz
    graviton_energy = HBAR * gw_omega
    graviton_equivalent_count = half_cycle_delta_energy / graviton_energy

    coherent_shot_phase = 1.0 / sqrt(photon_count)
    shot_noise_snr = relative_phase / coherent_shot_phase
    effective_path_length_m = C * b.delay_time

    # tau_min follows directly from h Omega tau sqrt(N) >= target_snr.
    minimum_delay_for_target_snr = (
        b.target_snr
        / (b.strain * b.optical_omega * sqrt(photon_count))
    )
    minimum_path_for_target_snr_m = C * minimum_delay_for_target_snr

    # Independent optical-loss budget.  For small loss ell, survival after M
    # reflections is (1-ell)^M; exp(-M ell) is retained as the asymptotic check.
    exact_survival = (1.0 - b.per_reflection_loss) ** b.reflection_count
    exponential_survival = exp(-b.per_reflection_loss * b.reflection_count)
    half_survival_loss_budget = 1.0 - exp(log(0.5) / b.reflection_count)
    ten_percent_survival_loss_budget = 1.0 - exp(log(0.1) / b.reflection_count)

    return {
        "photon_energy_J": photon_energy,
        "photon_count": photon_count,
        "single_arm_delta_omega_s^-1": single_arm_delta_omega,
        "differential_delta_omega_s^-1": differential_delta_omega,
        "relative_phase_rad": relative_phase,
        "half_cycle_delta_energy_J": half_cycle_delta_energy,
        "gw_graviton_energy_J": graviton_energy,
        "graviton_equivalent_count": graviton_equivalent_count,
        "coherent_shot_phase_rad": coherent_shot_phase,
        "shot_noise_snr_ideal": shot_noise_snr,
        "effective_path_length_m": effective_path_length_m,
        "minimum_delay_for_target_snr_s": minimum_delay_for_target_snr,
        "minimum_path_for_target_snr_m": minimum_path_for_target_snr_m,
        "optical_survival_fraction": exact_survival,
        "optical_survival_exp_approx": exponential_survival,
        "loss_per_reflection_for_50pct_survival": half_survival_loss_budget,
        "loss_per_reflection_for_10pct_survival": ten_percent_survival_loss_budget,
    }


def verify(b: Benchmark = Benchmark()) -> dict[str, float]:
    r = evaluate(b)

    # Algebraic source-law checks.
    assert abs(r["differential_delta_omega_s^-1"] - b.strain * b.optical_omega) <= 1e-30
    assert abs(r["relative_phase_rad"] - b.strain * b.optical_omega * b.delay_time) <= 1e-30
    assert abs(r["half_cycle_delta_energy_J"] - 0.5 * b.strain * b.pulse_energy) <= 1e-40

    # Paper-scale sanity windows, deliberately loose/order-of-magnitude.
    assert 1e15 <= r["photon_count"] <= 1e17
    assert 1e-8 <= r["differential_delta_omega_s^-1"] <= 1e-6
    assert 1e-8 <= r["relative_phase_rad"] <= 1e-6
    assert 1e-9 <= r["coherent_shot_phase_rad"] <= 1e-7
    assert r["shot_noise_snr_ideal"] > 1.0
    assert r["graviton_equivalent_count"] > 1.0
    assert 1e8 <= r["effective_path_length_m"] <= 2e9

    # Design-tradeoff checks.
    assert 0.05 <= r["minimum_delay_for_target_snr_s"] <= 0.2
    assert 1e7 <= r["minimum_path_for_target_snr_m"] <= 1e8
    assert abs(r["optical_survival_fraction"] - r["optical_survival_exp_approx"]) < 1e-6
    assert 5e-7 <= r["loss_per_reflection_for_50pct_survival"] <= 1e-6
    assert 2e-6 <= r["loss_per_reflection_for_10pct_survival"] <= 3e-6

    return r


if __name__ == "__main__":
    result = verify()
    for key, value in result.items():
        print(f"{key}={value:.12g}")
