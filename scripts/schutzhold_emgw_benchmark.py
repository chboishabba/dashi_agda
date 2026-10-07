#!/usr/bin/env python3
"""Executable benchmark for Schuetzhold controlled EM<->GW exchange.

Source benchmark (arXiv:2502.10221 / PRL 135, 171501):
  h ~ 1e-22, optical angular frequency Omega ~ 1e15 s^-1,
  pulse energy ~ mJ, GW angular frequency ~ 2*pi*kHz,
  phase accumulation time of a few seconds.

This script checks the algebraic consequences used by the formal lane.  It is
not an apparatus noise model and does not claim experimental observation.
"""

from dataclasses import dataclass
from math import pi, sqrt

HBAR = 1.054_571_817e-34  # J s, rounded numerical realization
C = 299_792_458.0  # m/s, exact SI value represented as float here


@dataclass(frozen=True)
class Benchmark:
    strain: float = 1.0e-22
    optical_omega: float = 1.0e15  # rad/s order-of-magnitude benchmark
    pulse_energy: float = 1.0e-3  # J
    gw_frequency_hz: float = 1.0e3
    delay_time: float = 3.0  # s


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

    return r


if __name__ == "__main__":
    result = verify()
    for key, value in result.items():
        print(f"{key}={value:.12g}")
