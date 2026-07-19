#!/usr/bin/env python3
"""Canonical entry point for the compact-Gamma pathwise retention audit.

The pathwise audit reconstructs calibration and held-out trajectories from the
finite packet net.  During matched-cutoff verification the source profiles
already carry the exact Fourier constructor seed that produced the selected
state.  Re-feeding that value through ``build_split_profiles`` would apply the
split helper's seed-derivation convention a second time and therefore construct
a different packet.

This driver installs a narrow replacement only for the ``matched-member`` and
``matched-center`` splits.  Those profiles are rebuilt directly with
``build_profile`` and the original source seed.  Every other split continues to
use the shared finite-net builder unchanged.
"""
from __future__ import annotations

from dataclasses import asdict
from typing import Any

import ns_compact_gamma_pathwise_retention_audit as pathwise
from ns_compact_gamma_common_u_net_audit import PacketParameters, build_profile


_original_build_split_profiles = pathwise.build_split_profiles


def build_split_profiles_with_exact_matched_seed(
    *,
    split: str,
    base_parameters: tuple[PacketParameters, ...],
    seeds: tuple[int, ...],
    samples_per_base: int,
    perturb: bool,
    phase_jitter: float,
    log_ratio_jitter: float,
    log_satellite_jitter: float,
    cutoff: int,
    target_shells: tuple[int, ...],
    nu: float,
    input_amplitude: float,
    target_packet_energy: float,
    gamma_threshold: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
) -> list[dict[str, Any]]:
    """Preserve the selected packet seed during matched-cutoff reconstruction."""
    if split not in {"matched-member", "matched-center"}:
        return _original_build_split_profiles(
            split=split,
            base_parameters=base_parameters,
            seeds=seeds,
            samples_per_base=samples_per_base,
            perturb=perturb,
            phase_jitter=phase_jitter,
            log_ratio_jitter=log_ratio_jitter,
            log_satellite_jitter=log_satellite_jitter,
            cutoff=cutoff,
            target_shells=target_shells,
            nu=nu,
            input_amplitude=input_amplitude,
            target_packet_energy=target_packet_energy,
            gamma_threshold=gamma_threshold,
            end_parabolic_time=end_parabolic_time,
            output_count=output_count,
            cfl=cfl,
        )

    if perturb:
        raise ValueError("matched-cutoff reconstruction must not perturb parameters")
    if samples_per_base != 1:
        raise ValueError("matched-cutoff reconstruction requires one sample")
    if len(base_parameters) != 1 or len(seeds) != 1 or len(target_shells) != 1:
        raise ValueError(
            "matched-cutoff reconstruction requires one parameter, seed, and shell"
        )
    if any(value != 0.0 for value in (
        phase_jitter,
        log_ratio_jitter,
        log_satellite_jitter,
    )):
        raise ValueError("matched-cutoff reconstruction requires zero jitter")

    parameters = base_parameters[0]
    source_seed = int(seeds[0])
    shell = int(target_shells[0])
    profile = build_profile(
        split=split,
        seed=source_seed,
        parameters=parameters,
        cutoff=cutoff,
        target_shell=shell,
        nu=nu,
        input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    profile["base_parameters"] = asdict(parameters)
    profile["perturbation_sample_index"] = 0
    profile["derived_state_seed"] = source_seed
    return [profile]


def install_exact_matched_seed_builder() -> None:
    pathwise.build_split_profiles = build_split_profiles_with_exact_matched_seed


def main() -> None:
    install_exact_matched_seed_builder()
    pathwise.main()


if __name__ == "__main__":
    main()
