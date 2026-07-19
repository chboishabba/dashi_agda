#!/usr/bin/env python3
"""Adversarially exercise the integrated compact-Gamma remainder and its local oscillation.

The common-U net audit can close trivially when one fitted pointwise theta absorbs
all sampled profiles, giving C_theta = 0.  This lane deliberately separates the
roles:

- center profiles fit theta and c_lambda;
- calibration profiles fit a one-sided oscillation allowance for C_theta;
- held-out profiles test that allowance;
- matched cutoffs test the worst held-out perturbations.

Calibration and holdout profiles are deterministic perturbations of a coarse
normalized multi-triad center net.  Pointwise violations of R <= theta E are not
silently treated as failure: their positive excess is integrated as

    C_theta = integral max(R - theta E, 0) d tau.

This is finite-Galerkin proof search only.  It does not establish an analytic
local Lipschitz estimate, compactness, BKM continuation, or Clay authority.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict
from pathlib import Path
from typing import Any

import numpy as np

from ns_compact_gamma_common_u_net_audit import (
    PacketParameters,
    atomic_json,
    build_profile,
    check_danger_constants,
    fit_local_oscillation,
    fit_theta_and_c_lambda,
    integrate_profile_remainder,
    packet_parameter_grid,
    parse_float_tuple,
    parse_int_tuple,
    strip_profile,
)


def jitter_parameters(
    base: PacketParameters,
    *,
    seed: int,
    sample_index: int,
    phase_jitter: float,
    log_ratio_jitter: float,
    log_satellite_jitter: float,
) -> PacketParameters:
    if min(phase_jitter, log_ratio_jitter, log_satellite_jitter) < 0.0:
        raise ValueError("jitter magnitudes must be nonnegative")
    rng = np.random.default_rng(seed * 1_000_003 + sample_index * 97_409 + 17)
    phase = max(0.0, base.phase_spread + phase_jitter * float(rng.normal()))
    ratio = base.target_ratio * math.exp(log_ratio_jitter * float(rng.normal()))
    satellite = base.satellite_fraction * math.exp(
        log_satellite_jitter * float(rng.normal())
    )
    satellite = min(max(satellite, 0.1), 1.0)
    return PacketParameters(
        triad_count=base.triad_count,
        phase_spread=phase,
        target_ratio=ratio,
        satellite_fraction=satellite,
    )


def annotate_profile(
    profile: dict[str, Any],
    *,
    base: PacketParameters,
    sample_index: int,
    derived_seed: int,
) -> dict[str, Any]:
    profile["base_parameters"] = asdict(base)
    profile["perturbation_sample_index"] = sample_index
    profile["derived_state_seed"] = derived_seed
    return profile


def build_split_profiles(
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
    if samples_per_base < 1:
        raise ValueError("samples per base must be positive")
    profiles: list[dict[str, Any]] = []
    for seed in seeds:
        for base_index, base in enumerate(base_parameters):
            count = samples_per_base if perturb else 1
            for sample_index in range(count):
                parameters = (
                    jitter_parameters(
                        base,
                        seed=seed + 101 * base_index,
                        sample_index=sample_index,
                        phase_jitter=phase_jitter,
                        log_ratio_jitter=log_ratio_jitter,
                        log_satellite_jitter=log_satellite_jitter,
                    )
                    if perturb
                    else base
                )
                derived_seed = seed * 10_000 + base_index * 100 + sample_index + 1
                for shell in target_shells:
                    profile = build_profile(
                        split=split,
                        seed=derived_seed,
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
                    profiles.append(
                        annotate_profile(
                            profile,
                            base=base,
                            sample_index=sample_index,
                            derived_seed=derived_seed,
                        )
                    )
    return profiles


def pointwise_violation_summary(
    profiles: list[dict[str, Any]], theta: float
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for profile in profiles:
        for row in profile["rows"]:
            accounting = row.get("mechanism_accounting")
            if accounting is None:
                raise ValueError("unresolved compact-Gamma branch")
            escape = float(accounting["escape_supply"])
            replenishment = float(accounting["replenishment"])
            excess = max(replenishment - theta * escape, 0.0)
            if excess > 1.0e-12:
                rows.append(
                    {
                        "profile_id": profile["profile_id"],
                        "parabolic_time": float(row["parabolic_time"]),
                        "gamma": float(row["gamma"]),
                        "escape_supply": escape,
                        "replenishment": replenishment,
                        "pointwise_excess": excess,
                    }
                )
    return {
        "violation_row_count": len(rows),
        "maximum_pointwise_excess": max(
            (row["pointwise_excess"] for row in rows), default=0.0
        ),
        "rows": rows,
    }


def audit_family(
    *,
    search_cutoff: int,
    verify_cutoffs: tuple[int, ...],
    target_shells: tuple[int, ...],
    nu: float,
    input_amplitude: float,
    target_packet_energy: float,
    base_parameters: tuple[PacketParameters, ...],
    center_seeds: tuple[int, ...],
    calibration_seeds: tuple[int, ...],
    holdout_seeds: tuple[int, ...],
    samples_per_base: int,
    calibration_jitter_scale: float,
    holdout_jitter_scale: float,
    phase_jitter: float,
    log_ratio_jitter: float,
    log_satellite_jitter: float,
    gamma_threshold: float,
    theta_slack: float,
    c_lambda_slack: float,
    slope_slack: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
    verify_count: int,
) -> dict[str, Any]:
    all_seeds = center_seeds + calibration_seeds + holdout_seeds
    if len(all_seeds) != len(set(all_seeds)):
        raise ValueError("center, calibration, and holdout seeds must be disjoint")
    if not 0.0 <= calibration_jitter_scale <= holdout_jitter_scale:
        raise ValueError("require 0 <= calibration jitter scale <= holdout jitter scale")
    if verify_count < 1:
        raise ValueError("verify count must be positive")

    centers = build_split_profiles(
        split="center",
        base_parameters=base_parameters,
        seeds=center_seeds,
        samples_per_base=1,
        perturb=False,
        phase_jitter=0.0,
        log_ratio_jitter=0.0,
        log_satellite_jitter=0.0,
        cutoff=search_cutoff,
        target_shells=target_shells,
        nu=nu,
        input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    calibration = build_split_profiles(
        split="calibration",
        base_parameters=base_parameters,
        seeds=calibration_seeds,
        samples_per_base=samples_per_base,
        perturb=True,
        phase_jitter=calibration_jitter_scale * phase_jitter,
        log_ratio_jitter=calibration_jitter_scale * log_ratio_jitter,
        log_satellite_jitter=calibration_jitter_scale * log_satellite_jitter,
        cutoff=search_cutoff,
        target_shells=target_shells,
        nu=nu,
        input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    holdout = build_split_profiles(
        split="holdout",
        base_parameters=base_parameters,
        seeds=holdout_seeds,
        samples_per_base=samples_per_base,
        perturb=True,
        phase_jitter=holdout_jitter_scale * phase_jitter,
        log_ratio_jitter=holdout_jitter_scale * log_ratio_jitter,
        log_satellite_jitter=holdout_jitter_scale * log_satellite_jitter,
        cutoff=search_cutoff,
        target_shells=target_shells,
        nu=nu,
        input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )

    fitted = fit_theta_and_c_lambda(
        centers,
        gamma_threshold=gamma_threshold,
        theta_slack=theta_slack,
        c_lambda_slack=c_lambda_slack,
    )
    theta = float(fitted["fitted_theta"])
    c_lambda = float(fitted["fitted_c_lambda"])
    all_profiles = centers + calibration + holdout
    for profile in all_profiles:
        profile["envelope"] = integrate_profile_remainder(profile["rows"], theta)

    finite_net = fit_local_oscillation(
        centers, calibration, holdout, slope_slack=slope_slack
    )
    split_checks = {
        "center": check_danger_constants(centers, theta, c_lambda),
        "calibration": check_danger_constants(calibration, theta, c_lambda),
        "holdout": check_danger_constants(holdout, theta, c_lambda),
    }
    violations = {
        "center": pointwise_violation_summary(centers, theta),
        "calibration": pointwise_violation_summary(calibration, theta),
        "holdout": pointwise_violation_summary(holdout, theta),
    }

    nonzero_remainder_profiles = [
        profile
        for profile in all_profiles
        if float(profile["envelope"]["remainder_C_theta"]) > 1.0e-14
    ]
    ranked_holdout = sorted(
        holdout,
        key=lambda profile: (
            -float(profile["envelope"]["remainder_C_theta"]),
            -max(float(row["gamma"]) for row in profile["rows"]),
        ),
    )
    selected = ranked_holdout[:verify_count]
    matched_profiles: list[dict[str, Any]] = []
    for selected_profile in selected:
        parameters = PacketParameters(**selected_profile["parameters"])
        state_seed = int(selected_profile["derived_state_seed"])
        for cutoff in verify_cutoffs:
            for shell in target_shells:
                profile = build_profile(
                    split="matched-holdout",
                    seed=state_seed,
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
                profile["base_parameters"] = selected_profile["base_parameters"]
                profile["perturbation_sample_index"] = selected_profile[
                    "perturbation_sample_index"
                ]
                profile["derived_state_seed"] = state_seed
                profile["envelope"] = integrate_profile_remainder(
                    profile["rows"], theta
                )
                matched_profiles.append(profile)

    matched_checks = check_danger_constants(matched_profiles, theta, c_lambda)
    matched_violations = pointwise_violation_summary(matched_profiles, theta)
    common_upper = float(finite_net["common_member_upper_1_plus_remainder"])
    matched_upper_violations = [
        profile
        for profile in matched_profiles
        if float(profile["envelope"]["member_upper_B0_plus_C"])
        > common_upper + 1.0e-10
    ]

    group_map: dict[tuple[str, int], list[dict[str, Any]]] = {}
    for profile in matched_profiles:
        key = (str(profile["parameters"]), int(profile["target_shell"]))
        group_map.setdefault(key, []).append(profile)
    matched_groups: list[dict[str, Any]] = []
    for (parameters_key, shell), group in group_map.items():
        group.sort(key=lambda profile: int(profile["cutoff"]))
        remainders = [
            float(profile["envelope"]["remainder_C_theta"]) for profile in group
        ]
        uppers = [
            float(profile["envelope"]["member_upper_B0_plus_C"])
            for profile in group
        ]
        matched_groups.append(
            {
                "parameters": parameters_key,
                "target_shell": shell,
                "observed_cutoffs": [int(profile["cutoff"]) for profile in group],
                "matched_cutoff_complete": set(int(profile["cutoff"]) for profile in group)
                == set(verify_cutoffs),
                "remainder_spread": max(remainders) - min(remainders),
                "member_upper_spread": max(uppers) - min(uppers),
                "maximum_remainder": max(remainders),
                "maximum_member_upper": max(uppers),
                "below_common_upper": max(uppers) <= common_upper + 1.0e-10,
            }
        )

    all_rows = [
        row for profile in all_profiles + matched_profiles for row in profile["rows"]
    ]
    divergence_residuals = [
        float(row["angular_packet_metrics"]["relative_divergence_residual"])
        for row in all_rows
    ]
    mechanism_residuals = [
        float(row["mechanism_accounting"]["mechanism_balance_residual"])
        for row in all_rows
        if row["mechanism_accounting"] is not None
    ]
    fd_residuals = [
        float(row["finite_difference_residual"])
        for row in all_rows
        if row["finite_difference_residual"] is not None
    ]

    full_chain_survives = (
        bool(fitted["strict_theta"])
        and bool(fitted["positive_c_lambda"])
        and split_checks["center"]["all_dangerous_rows_absorbed"]
        and all(
            check["all_dangerous_rows_spend_c_lambda"]
            for check in split_checks.values()
        )
        and bool(finite_net["sampled_finite_net_bound_survives_holdout"])
        and matched_checks["all_dangerous_rows_spend_c_lambda"]
        and not matched_upper_violations
        and bool(matched_groups)
        and all(group["matched_cutoff_complete"] for group in matched_groups)
    )
    margin_rate = (1.0 - theta) * c_lambda
    residence_coefficient = common_upper / margin_rate if margin_rate > 0 else math.inf

    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_remainder_oscillation_audit": True,
            "center_only_danger_constant_fit": True,
            "integrated_remainder_exercised": bool(nonzero_remainder_profiles),
            "sampled_full_chain_survives": full_chain_survives,
            "analytic_remainder_oscillation_proved": False,
            "cutoff_shell_uniform_authority": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "pointwise_excess": "max(R_K-theta E_K,0)",
            "C_theta": "trapezoidal parabolic-time integral of pointwise excess",
            "local_oscillation": "one-sided change in C_theta divided by Fourier-state L2 distance",
        },
        "parameters": {
            "search_cutoff": search_cutoff,
            "verify_cutoffs": list(verify_cutoffs),
            "target_shells": list(target_shells),
            "viscosity": nu,
            "input_amplitude_before_normalization": input_amplitude,
            "target_packet_energy": target_packet_energy,
            "base_parameters": [asdict(parameter) for parameter in base_parameters],
            "center_seeds": list(center_seeds),
            "calibration_seeds": list(calibration_seeds),
            "holdout_seeds": list(holdout_seeds),
            "samples_per_base": samples_per_base,
            "calibration_jitter_scale": calibration_jitter_scale,
            "holdout_jitter_scale": holdout_jitter_scale,
            "phase_jitter": phase_jitter,
            "log_ratio_jitter": log_ratio_jitter,
            "log_satellite_jitter": log_satellite_jitter,
            "gamma_threshold": gamma_threshold,
            "theta_slack": theta_slack,
            "c_lambda_slack": c_lambda_slack,
            "slope_slack": slope_slack,
            "end_parabolic_time": end_parabolic_time,
            "output_count": output_count,
            "cfl": cfl,
            "verify_count": verify_count,
        },
        "center_profile_count": len(centers),
        "calibration_profile_count": len(calibration),
        "holdout_profile_count": len(holdout),
        "matched_profile_count": len(matched_profiles),
        "fitted_danger_constants": fitted,
        "split_danger_constant_checks": split_checks,
        "pointwise_violation_summaries": violations,
        "nonzero_remainder_profile_count": len(nonzero_remainder_profiles),
        "maximum_profile_remainder": max(
            (
                float(profile["envelope"]["remainder_C_theta"])
                for profile in all_profiles
            ),
            default=0.0,
        ),
        "finite_net_remainder_envelope": finite_net,
        "sampled_common_member_upper": common_upper,
        "sampled_margin_consumption_rate": margin_rate,
        "sampled_residence_coefficient": residence_coefficient,
        "matched_danger_constant_checks": matched_checks,
        "matched_pointwise_violation_summary": matched_violations,
        "matched_upper_violation_count": len(matched_upper_violations),
        "matched_cutoff_groups": matched_groups,
        "maximum_matched_remainder_spread": max(
            (group["remainder_spread"] for group in matched_groups), default=None
        ),
        "maximum_matched_member_upper_spread": max(
            (group["member_upper_spread"] for group in matched_groups), default=None
        ),
        "maximum_relative_divergence_residual": max(divergence_residuals, default=None),
        "maximum_mechanism_balance_residual": max(mechanism_residuals, default=None),
        "maximum_finite_difference_residual": max(fd_residuals, default=None),
        "centers": [strip_profile(profile) for profile in centers],
        "calibration_profiles": [strip_profile(profile) for profile in calibration],
        "holdout_profiles": [strip_profile(profile) for profile in holdout],
        "matched_profiles": [strip_profile(profile) for profile in matched_profiles],
        "limitations": [
            "jittered finite profiles are not a continuum compactness proof",
            "fitted one-sided slopes are not analytic local Lipschitz constants",
            "matched cutoffs do not prove cutoff-uniform convergence",
            "sampled constants do not construct Agda proof terms",
            "no BKM, global-regularity, or Clay promotion",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--search-cutoff", type=int, default=24)
    parser.add_argument("--verify-cutoffs", default="32,48,64")
    parser.add_argument("--target-shells", default="2,3")
    parser.add_argument("--viscosity", type=float, default=0.01)
    parser.add_argument("--input-amplitude", type=float, default=0.1)
    parser.add_argument("--target-packet-energy", type=float, default=0.86)
    parser.add_argument("--triad-counts", default="4")
    parser.add_argument("--phase-spreads", default="0.0")
    parser.add_argument("--target-ratios", default="2.5")
    parser.add_argument("--satellite-fractions", default="0.55")
    parser.add_argument("--center-seeds", default="1")
    parser.add_argument("--calibration-seeds", default="2")
    parser.add_argument("--holdout-seeds", default="3")
    parser.add_argument("--samples-per-base", type=int, default=4)
    parser.add_argument("--calibration-jitter-scale", type=float, default=0.7)
    parser.add_argument("--holdout-jitter-scale", type=float, default=1.0)
    parser.add_argument("--phase-jitter", type=float, default=0.8)
    parser.add_argument("--log-ratio-jitter", type=float, default=0.5)
    parser.add_argument("--log-satellite-jitter", type=float, default=0.35)
    parser.add_argument("--gamma-threshold", type=float, default=0.5)
    parser.add_argument("--theta-slack", type=float, default=0.005)
    parser.add_argument("--c-lambda-slack", type=float, default=0.05)
    parser.add_argument("--slope-slack", type=float, default=0.15)
    parser.add_argument("--end-parabolic-time", type=float, default=0.004)
    parser.add_argument("--output-count", type=int, default=3)
    parser.add_argument("--cfl", type=float, default=0.2)
    parser.add_argument("--verify-count", type=int, default=1)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    base_parameters = packet_parameter_grid(
        parse_int_tuple(args.triad_counts),
        parse_float_tuple(args.phase_spreads),
        parse_float_tuple(args.target_ratios),
        parse_float_tuple(args.satellite_fractions),
    )
    result = audit_family(
        search_cutoff=args.search_cutoff,
        verify_cutoffs=parse_int_tuple(args.verify_cutoffs),
        target_shells=parse_int_tuple(args.target_shells),
        nu=args.viscosity,
        input_amplitude=args.input_amplitude,
        target_packet_energy=args.target_packet_energy,
        base_parameters=base_parameters,
        center_seeds=parse_int_tuple(args.center_seeds),
        calibration_seeds=parse_int_tuple(args.calibration_seeds),
        holdout_seeds=parse_int_tuple(args.holdout_seeds),
        samples_per_base=args.samples_per_base,
        calibration_jitter_scale=args.calibration_jitter_scale,
        holdout_jitter_scale=args.holdout_jitter_scale,
        phase_jitter=args.phase_jitter,
        log_ratio_jitter=args.log_ratio_jitter,
        log_satellite_jitter=args.log_satellite_jitter,
        gamma_threshold=args.gamma_threshold,
        theta_slack=args.theta_slack,
        c_lambda_slack=args.c_lambda_slack,
        slope_slack=args.slope_slack,
        end_parabolic_time=args.end_parabolic_time,
        output_count=args.output_count,
        cfl=args.cfl,
        verify_count=args.verify_count,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(
        json.dumps(
            {
                "output_json": str(args.output_json),
                "fitted_theta": result["fitted_danger_constants"]["fitted_theta"],
                "nonzero_remainder_profile_count": result[
                    "nonzero_remainder_profile_count"
                ],
                "holdout_net_violations": result["finite_net_remainder_envelope"][
                    "holdout_violation_count"
                ],
                "sampled_full_chain_survives": result["authority"][
                    "sampled_full_chain_survives"
                ],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
