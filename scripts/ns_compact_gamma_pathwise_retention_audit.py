#!/usr/bin/env python3
"""Test local-to-global compact-Gamma retention along normalized packet paths.

The retained danger audit found finite endpoint moduli

    Gamma(member) - Gamma(center) <= L_Gamma d,
    log(E_center/E_member)_+      <= L_E d.

This lane asks whether those endpoint bounds arise from a stable local mechanism.
For every dangerous calibration or held-out center/member pair, it constructs a
normalized chord path on the fixed target-packet-energy surface, evaluates the
exact compact-Gamma mechanism accounting at path samples, and fits segmentwise
Lipschitz constants.  Local estimates are composed using path arc length:

    Gamma(member) <= Gamma(center) + L_Gamma * length(path),
    E(member)     >= exp(-L_E * length(path)) * E(center).

The most adverse held-out paths are rebuilt at N32/N48/N64 and shells 2/3.
This is finite-Galerkin proof search, not an analytic path-continuity theorem.
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
    mechanism_rates,
    nearest_center,
    normalize_packet_energy,
    packet_parameter_grid,
    parse_float_tuple,
    parse_int_tuple,
    state_feature,
    strip_profile,
)
from ns_compact_gamma_multitriad_evolved_audit import (
    evolved_states,
    multitriad_diffuse_hat,
)
from ns_compact_gamma_potential_audit import compact_gamma_snapshot
from ns_compact_gamma_replenishment_audit import mechanism_accounting
from ns_compact_gamma_remainder_oscillation_audit import build_split_profiles


def reconstruct_trajectory(
    profile: dict[str, Any],
    *,
    nu: float,
    input_amplitude: float,
    target_packet_energy: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
) -> list[dict[str, Any]]:
    parameters = PacketParameters(**profile["parameters"])
    cutoff = int(profile["cutoff"])
    shell = int(profile["target_shell"])
    raw, _metadata = multitriad_diffuse_hat(
        cutoff,
        shell,
        triad_count=parameters.triad_count,
        input_amplitude=input_amplitude,
        target_ratio=parameters.target_ratio,
        satellite_fraction=parameters.satellite_fraction,
        phase_spread=parameters.phase_spread,
        seed=int(profile["derived_state_seed"]),
    )
    raw, normalization = normalize_packet_energy(
        raw, shell, target_packet_energy
    )
    trajectory = evolved_states(
        raw,
        nu,
        shell,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    for state in trajectory:
        state["normalization"] = normalization
    return trajectory


def state_at_time(
    trajectory: list[dict[str, Any]], parabolic_time: float
) -> np.ndarray:
    matches = [
        state
        for state in trajectory
        if math.isclose(
            float(state["parabolic_time"]),
            parabolic_time,
            rel_tol=0.0,
            abs_tol=1.0e-12,
        )
    ]
    if len(matches) != 1:
        raise ValueError(f"expected one reconstructed state at tau={parabolic_time}")
    return np.asarray(matches[0]["raw_hat"], dtype=np.complex128)


def compact_path_sample(
    raw_hat: np.ndarray,
    *,
    nu: float,
    target_shell: int,
) -> dict[str, Any]:
    snapshot = compact_gamma_snapshot(raw_hat, nu, target_shell)
    if snapshot["positive_part_branch"] == "positive_part_kink_unresolved":
        return {
            "resolved": False,
            "positive_part_branch": snapshot["positive_part_branch"],
            "gamma": float(snapshot["gamma"]),
            "compact_potential": float(snapshot["compact_gamma_potential_B"]),
            "feature": state_feature(raw_hat),
        }
    accounting = mechanism_accounting(snapshot)
    escape = float(accounting["escape_supply"])
    replenishment = float(accounting["replenishment"])
    return {
        "resolved": True,
        "positive_part_branch": snapshot["positive_part_branch"],
        "gamma": float(snapshot["gamma"]),
        "compact_potential": float(snapshot["compact_gamma_potential_B"]),
        "escape_supply": escape,
        "replenishment": replenishment,
        "feature": state_feature(raw_hat),
        "mechanism_balance_residual": float(
            accounting["mechanism_balance_residual"]
        ),
        "finite_difference_residual": snapshot["finite_difference_check"][
            "residual"
        ],
        "state_rhs_component_sum_max_residual": float(
            snapshot["state_rhs_component_sum_max_residual"]
        ),
    }


def normalized_chord_path(
    center_raw: np.ndarray,
    member_raw: np.ndarray,
    *,
    nu: float,
    target_shell: int,
    target_packet_energy: float,
    path_sample_count: int,
) -> dict[str, Any]:
    if path_sample_count < 2:
        raise ValueError("path sample count must be at least two")
    if center_raw.shape != member_raw.shape:
        raise ValueError("path endpoints must have the same Galerkin cutoff")
    samples: list[dict[str, Any]] = []
    for index, parameter in enumerate(np.linspace(0.0, 1.0, path_sample_count)):
        raw = (1.0 - float(parameter)) * center_raw + float(parameter) * member_raw
        raw, normalization = normalize_packet_energy(
            raw, target_shell, target_packet_energy
        )
        sample = compact_path_sample(raw, nu=nu, target_shell=target_shell)
        sample.update(
            {
                "path_index": index,
                "path_parameter": float(parameter),
                "normalization_residual": float(
                    normalization["normalization_residual"]
                ),
            }
        )
        samples.append(sample)

    segments: list[dict[str, Any]] = []
    arc_length = 0.0
    positive_gamma_variation = 0.0
    positive_log_escape_loss = 0.0
    unresolved_segment_count = 0
    for left, right in zip(samples, samples[1:]):
        length = float(np.linalg.norm(right["feature"] - left["feature"]))
        arc_length += length
        if not left["resolved"] or not right["resolved"]:
            unresolved_segment_count += 1
            segments.append(
                {
                    "left_index": left["path_index"],
                    "right_index": right["path_index"],
                    "segment_length": length,
                    "resolved": False,
                }
            )
            continue
        if left["escape_supply"] <= 0.0 or right["escape_supply"] <= 0.0:
            unresolved_segment_count += 1
            segments.append(
                {
                    "left_index": left["path_index"],
                    "right_index": right["path_index"],
                    "segment_length": length,
                    "resolved": False,
                    "reason": "nonpositive escape supply",
                }
            )
            continue
        gamma_rise = max(right["gamma"] - left["gamma"], 0.0)
        log_escape_loss = max(
            math.log(left["escape_supply"])
            - math.log(right["escape_supply"]),
            0.0,
        )
        positive_gamma_variation += gamma_rise
        positive_log_escape_loss += log_escape_loss
        if length <= 1.0e-14:
            gamma_slope = 0.0 if gamma_rise <= 1.0e-12 else math.inf
            log_escape_slope = 0.0 if log_escape_loss <= 1.0e-12 else math.inf
        else:
            gamma_slope = gamma_rise / length
            log_escape_slope = log_escape_loss / length
        segments.append(
            {
                "left_index": left["path_index"],
                "right_index": right["path_index"],
                "segment_length": length,
                "resolved": True,
                "positive_gamma_rise": gamma_rise,
                "positive_log_escape_loss": log_escape_loss,
                "gamma_lipschitz_quotient": gamma_slope,
                "log_escape_lipschitz_quotient": log_escape_slope,
            }
        )

    chord_distance = float(
        np.linalg.norm(samples[-1]["feature"] - samples[0]["feature"])
    )
    resolved = unresolved_segment_count == 0 and all(
        sample["resolved"] for sample in samples
    )
    endpoint_gamma_rise = max(samples[-1]["gamma"] - samples[0]["gamma"], 0.0)
    if resolved:
        endpoint_log_escape_loss = max(
            math.log(samples[0]["escape_supply"])
            - math.log(samples[-1]["escape_supply"]),
            0.0,
        )
        minimum_escape = min(float(sample["escape_supply"]) for sample in samples)
    else:
        endpoint_log_escape_loss = None
        minimum_escape = None
    return {
        "resolved": resolved,
        "path_sample_count": len(samples),
        "arc_length": arc_length,
        "chord_distance": chord_distance,
        "arc_over_chord": arc_length / chord_distance if chord_distance > 0.0 else 1.0,
        "endpoint_gamma_rise": endpoint_gamma_rise,
        "endpoint_log_escape_loss": endpoint_log_escape_loss,
        "positive_gamma_variation": positive_gamma_variation,
        "positive_log_escape_variation": positive_log_escape_loss,
        "minimum_escape_supply": minimum_escape,
        "unresolved_segment_count": unresolved_segment_count,
        "samples": [
            {key: value for key, value in sample.items() if key != "feature"}
            for sample in samples
        ],
        "segments": segments,
    }


def build_dangerous_paths(
    profiles: list[dict[str, Any]],
    centers: list[dict[str, Any]],
    *,
    trajectory_cache: dict[str, list[dict[str, Any]]],
    nu: float,
    target_packet_energy: float,
    gamma_threshold: float,
    path_sample_count: int,
) -> list[dict[str, Any]]:
    paths: list[dict[str, Any]] = []
    for profile in profiles:
        center, _endpoint_distance = nearest_center(profile, centers)
        member_trajectory = trajectory_cache[profile["profile_id"]]
        center_trajectory = trajectory_cache[center["profile_id"]]
        for row in profile["rows"]:
            if float(row["gamma"]) + 1.0e-12 < gamma_threshold:
                continue
            time = float(row["parabolic_time"])
            member_raw = state_at_time(member_trajectory, time)
            center_raw = state_at_time(center_trajectory, time)
            receipt = normalized_chord_path(
                center_raw,
                member_raw,
                nu=nu,
                target_shell=int(profile["target_shell"]),
                target_packet_energy=target_packet_energy,
                path_sample_count=path_sample_count,
            )
            receipt.update(
                {
                    "profile_id": profile["profile_id"],
                    "center_profile_id": center["profile_id"],
                    "target_shell": int(profile["target_shell"]),
                    "cutoff": int(profile["cutoff"]),
                    "parabolic_time": time,
                    "member_gamma": float(row["gamma"]),
                    "member_escape": mechanism_rates(row)[0],
                }
            )
            paths.append(receipt)
    return paths


def fit_path_constants(
    paths: list[dict[str, Any]], *, slack: float
) -> dict[str, Any]:
    if not paths:
        raise ValueError("path calibration set is empty")
    if not math.isfinite(slack) or slack < 0.0:
        raise ValueError("path modulus slack must be finite and nonnegative")
    unresolved = [path for path in paths if not path["resolved"]]
    gamma_quotients = [
        float(segment["gamma_lipschitz_quotient"])
        for path in paths
        for segment in path["segments"]
        if segment.get("resolved", False)
    ]
    log_quotients = [
        float(segment["log_escape_lipschitz_quotient"])
        for path in paths
        for segment in path["segments"]
        if segment.get("resolved", False)
    ]
    singular = any(not math.isfinite(value) for value in gamma_quotients + log_quotients)
    if unresolved or singular:
        gamma_constant = math.inf
        log_constant = math.inf
    else:
        gamma_constant = max(gamma_quotients, default=0.0) * (1.0 + slack)
        log_constant = max(log_quotients, default=0.0) * (1.0 + slack)
    return {
        "path_count": len(paths),
        "unresolved_path_count": len(unresolved),
        "raw_gamma_lipschitz_constant": max(gamma_quotients, default=0.0),
        "raw_log_escape_lipschitz_constant": max(log_quotients, default=0.0),
        "fitted_gamma_lipschitz_constant": gamma_constant,
        "fitted_log_escape_lipschitz_constant": log_constant,
        "slack": slack,
        "finite_candidate": math.isfinite(gamma_constant) and math.isfinite(log_constant),
    }


def evaluate_paths(
    paths: list[dict[str, Any]],
    *,
    gamma_constant: float,
    log_escape_constant: float,
    gamma_threshold: float,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for path in paths:
        if not path["resolved"]:
            rows.append(
                {
                    "profile_id": path["profile_id"],
                    "target_shell": path["target_shell"],
                    "cutoff": path["cutoff"],
                    "parabolic_time": path["parabolic_time"],
                    "resolved": False,
                    "survives": False,
                }
            )
            continue
        center = path["samples"][0]
        member = path["samples"][-1]
        length = float(path["arc_length"])
        gamma_allowance = gamma_constant * length
        log_allowance = log_escape_constant * length
        retained_lower = math.exp(-log_allowance) * float(center["escape_supply"])
        gamma_margin = (
            float(center["gamma"])
            + gamma_allowance
            - float(member["gamma"])
        )
        retained_margin = float(member["escape_supply"]) - retained_lower
        buffered_threshold = max(gamma_threshold - gamma_allowance, 0.0)
        buffered_center_margin = float(center["gamma"]) - buffered_threshold
        segment_gamma_margins: list[float] = []
        segment_log_margins: list[float] = []
        for segment in path["segments"]:
            if not segment.get("resolved", False):
                segment_gamma_margins.append(-math.inf)
                segment_log_margins.append(-math.inf)
                continue
            segment_gamma_margins.append(
                gamma_constant * float(segment["segment_length"])
                - float(segment["positive_gamma_rise"])
            )
            segment_log_margins.append(
                log_escape_constant * float(segment["segment_length"])
                - float(segment["positive_log_escape_loss"])
            )
        survives = (
            gamma_margin >= -1.0e-10
            and retained_margin >= -1.0e-10
            and buffered_center_margin >= -1.0e-10
            and all(margin >= -1.0e-10 for margin in segment_gamma_margins)
            and all(margin >= -1.0e-10 for margin in segment_log_margins)
            and retained_lower > 0.0
        )
        rows.append(
            {
                "profile_id": path["profile_id"],
                "center_profile_id": path["center_profile_id"],
                "target_shell": path["target_shell"],
                "cutoff": path["cutoff"],
                "parabolic_time": path["parabolic_time"],
                "resolved": True,
                "arc_length": length,
                "chord_distance": path["chord_distance"],
                "gamma_allowance": gamma_allowance,
                "log_escape_allowance": log_allowance,
                "retention_factor": math.exp(-log_allowance),
                "candidate_member_lower": retained_lower,
                "gamma_margin": gamma_margin,
                "retained_escape_margin": retained_margin,
                "buffered_center_margin": buffered_center_margin,
                "minimum_segment_gamma_margin": min(segment_gamma_margins),
                "minimum_segment_log_escape_margin": min(segment_log_margins),
                "minimum_path_escape_supply": path["minimum_escape_supply"],
                "survives": survives,
            }
        )
    resolved_rows = [row for row in rows if row["resolved"]]
    surviving = bool(rows) and all(row["survives"] for row in rows)
    return {
        "path_count": len(rows),
        "resolved_path_count": len(resolved_rows),
        "unresolved_path_count": len(rows) - len(resolved_rows),
        "candidate_member_lower": min(
            (row["candidate_member_lower"] for row in resolved_rows), default=None
        ),
        "minimum_gamma_margin": min(
            (row["gamma_margin"] for row in resolved_rows), default=None
        ),
        "minimum_retained_escape_margin": min(
            (row["retained_escape_margin"] for row in resolved_rows), default=None
        ),
        "minimum_segment_gamma_margin": min(
            (row["minimum_segment_gamma_margin"] for row in resolved_rows), default=None
        ),
        "minimum_segment_log_escape_margin": min(
            (row["minimum_segment_log_escape_margin"] for row in resolved_rows), default=None
        ),
        "minimum_retention_factor": min(
            (row["retention_factor"] for row in resolved_rows), default=None
        ),
        "sampled_pathwise_modulus_survives": surviving,
        "rows": rows,
    }


def select_adverse_profiles(
    profiles: list[dict[str, Any]], verify_count: int
) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    for shell in sorted({int(profile["target_shell"]) for profile in profiles}):
        candidates = [profile for profile in profiles if int(profile["target_shell"]) == shell]
        candidates.sort(
            key=lambda profile: min(
                (
                    mechanism_rates(row)[0]
                    for row in profile["rows"]
                    if bool(row["dangerous"])
                ),
                default=math.inf,
            )
        )
        selected.extend(candidates[:verify_count])
    return selected


def build_profile_sets(
    *,
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
    cutoff: int,
    target_shells: tuple[int, ...],
    nu: float,
    input_amplitude: float,
    target_packet_energy: float,
    gamma_threshold: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    common = {
        "base_parameters": base_parameters,
        "samples_per_base": samples_per_base,
        "cutoff": cutoff,
        "target_shells": target_shells,
        "nu": nu,
        "input_amplitude": input_amplitude,
        "target_packet_energy": target_packet_energy,
        "gamma_threshold": gamma_threshold,
        "end_parabolic_time": end_parabolic_time,
        "output_count": output_count,
        "cfl": cfl,
    }
    centers = build_split_profiles(
        split="center",
        seeds=center_seeds,
        perturb=False,
        phase_jitter=0.0,
        log_ratio_jitter=0.0,
        log_satellite_jitter=0.0,
        **common,
    )
    calibration = build_split_profiles(
        split="calibration",
        seeds=calibration_seeds,
        perturb=True,
        phase_jitter=calibration_jitter_scale * phase_jitter,
        log_ratio_jitter=calibration_jitter_scale * log_ratio_jitter,
        log_satellite_jitter=calibration_jitter_scale * log_satellite_jitter,
        **common,
    )
    holdout = build_split_profiles(
        split="holdout",
        seeds=holdout_seeds,
        perturb=True,
        phase_jitter=holdout_jitter_scale * phase_jitter,
        log_ratio_jitter=holdout_jitter_scale * log_ratio_jitter,
        log_satellite_jitter=holdout_jitter_scale * log_satellite_jitter,
        **common,
    )
    return centers, calibration, holdout


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
    path_sample_count: int,
    modulus_slack: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
    verify_count: int,
) -> dict[str, Any]:
    centers, calibration, holdout = build_profile_sets(
        base_parameters=base_parameters,
        center_seeds=center_seeds,
        calibration_seeds=calibration_seeds,
        holdout_seeds=holdout_seeds,
        samples_per_base=samples_per_base,
        calibration_jitter_scale=calibration_jitter_scale,
        holdout_jitter_scale=holdout_jitter_scale,
        phase_jitter=phase_jitter,
        log_ratio_jitter=log_ratio_jitter,
        log_satellite_jitter=log_satellite_jitter,
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
    all_search_profiles = centers + calibration + holdout
    trajectory_cache = {
        profile["profile_id"]: reconstruct_trajectory(
            profile,
            nu=nu,
            input_amplitude=input_amplitude,
            target_packet_energy=target_packet_energy,
            end_parabolic_time=end_parabolic_time,
            output_count=output_count,
            cfl=cfl,
        )
        for profile in all_search_profiles
    }
    calibration_paths = build_dangerous_paths(
        calibration,
        centers,
        trajectory_cache=trajectory_cache,
        nu=nu,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        path_sample_count=path_sample_count,
    )
    holdout_paths = build_dangerous_paths(
        holdout,
        centers,
        trajectory_cache=trajectory_cache,
        nu=nu,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        path_sample_count=path_sample_count,
    )
    fitted = fit_path_constants(calibration_paths, slack=modulus_slack)
    holdout_evaluation = evaluate_paths(
        holdout_paths,
        gamma_constant=float(fitted["fitted_gamma_lipschitz_constant"]),
        log_escape_constant=float(fitted["fitted_log_escape_lipschitz_constant"]),
        gamma_threshold=gamma_threshold,
    )

    selected_holdout = select_adverse_profiles(holdout, verify_count)
    matched_paths: list[dict[str, Any]] = []
    matched_profile_count = 0
    for member_source in selected_holdout:
        center_source, _distance = nearest_center(member_source, centers)
        member_parameters = PacketParameters(**member_source["parameters"])
        center_parameters = PacketParameters(**center_source["parameters"])
        shell = int(member_source["target_shell"])
        for cutoff in verify_cutoffs:
            common = {
                "base_parameters": (member_parameters,),
                "samples_per_base": 1,
                "cutoff": cutoff,
                "target_shells": (shell,),
                "nu": nu,
                "input_amplitude": input_amplitude,
                "target_packet_energy": target_packet_energy,
                "gamma_threshold": gamma_threshold,
                "end_parabolic_time": end_parabolic_time,
                "output_count": output_count,
                "cfl": cfl,
            }
            member_profiles = build_split_profiles(
                split="matched-member",
                seeds=(int(member_source["derived_state_seed"]),),
                perturb=False,
                phase_jitter=0.0,
                log_ratio_jitter=0.0,
                log_satellite_jitter=0.0,
                **common,
            )
            center_common = dict(common)
            center_common["base_parameters"] = (center_parameters,)
            center_profiles = build_split_profiles(
                split="matched-center",
                seeds=(int(center_source["derived_state_seed"]),),
                perturb=False,
                phase_jitter=0.0,
                log_ratio_jitter=0.0,
                log_satellite_jitter=0.0,
                **center_common,
            )
            member_profile = member_profiles[0]
            center_profile = center_profiles[0]
            matched_profile_count += 1
            local_cache = {
                member_profile["profile_id"]: reconstruct_trajectory(
                    member_profile,
                    nu=nu,
                    input_amplitude=input_amplitude,
                    target_packet_energy=target_packet_energy,
                    end_parabolic_time=end_parabolic_time,
                    output_count=output_count,
                    cfl=cfl,
                ),
                center_profile["profile_id"]: reconstruct_trajectory(
                    center_profile,
                    nu=nu,
                    input_amplitude=input_amplitude,
                    target_packet_energy=target_packet_energy,
                    end_parabolic_time=end_parabolic_time,
                    output_count=output_count,
                    cfl=cfl,
                ),
            }
            matched_paths.extend(
                build_dangerous_paths(
                    member_profiles,
                    center_profiles,
                    trajectory_cache=local_cache,
                    nu=nu,
                    target_packet_energy=target_packet_energy,
                    gamma_threshold=gamma_threshold,
                    path_sample_count=path_sample_count,
                )
            )
    matched_evaluation = evaluate_paths(
        matched_paths,
        gamma_constant=float(fitted["fitted_gamma_lipschitz_constant"]),
        log_escape_constant=float(fitted["fitted_log_escape_lipschitz_constant"]),
        gamma_threshold=gamma_threshold,
    )

    group_map: dict[tuple[int, float], list[dict[str, Any]]] = {}
    for row in matched_evaluation["rows"]:
        group_map.setdefault(
            (int(row["target_shell"]), float(row["parabolic_time"])), []
        ).append(row)
    matched_groups: list[dict[str, Any]] = []
    for (shell, time), rows in sorted(group_map.items()):
        cutoffs = sorted({int(row["cutoff"]) for row in rows})
        lowers = [float(row["candidate_member_lower"]) for row in rows]
        arc_lengths = [float(row["arc_length"]) for row in rows]
        matched_groups.append(
            {
                "target_shell": shell,
                "parabolic_time": time,
                "observed_cutoffs": cutoffs,
                "matched_cutoff_complete": set(cutoffs) == set(verify_cutoffs),
                "candidate_lower_spread": max(lowers) - min(lowers),
                "arc_length_spread": max(arc_lengths) - min(arc_lengths),
                "all_paths_survive": all(row["survives"] for row in rows),
            }
        )

    all_paths = calibration_paths + holdout_paths + matched_paths
    balance_residuals = [
        float(sample["mechanism_balance_residual"])
        for path in all_paths
        for sample in path["samples"]
        if sample.get("resolved", False)
    ]
    fd_residuals = [
        float(sample["finite_difference_residual"])
        for path in all_paths
        for sample in path["samples"]
        if sample.get("resolved", False)
        and sample.get("finite_difference_residual") is not None
    ]
    normalization_residuals = [
        float(sample["normalization_residual"])
        for path in all_paths
        for sample in path["samples"]
    ]
    full_survival = (
        bool(fitted["finite_candidate"])
        and bool(holdout_evaluation["sampled_pathwise_modulus_survives"])
        and bool(matched_evaluation["sampled_pathwise_modulus_survives"])
        and bool(matched_groups)
        and all(group["matched_cutoff_complete"] for group in matched_groups)
    )
    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_pathwise_retention_audit": True,
            "sampled_pathwise_modulus_survives_holdout": bool(
                holdout_evaluation["sampled_pathwise_modulus_survives"]
            ),
            "sampled_pathwise_modulus_survives_matched_cutoffs": bool(
                matched_evaluation["sampled_pathwise_modulus_survives"]
            ),
            "sampled_full_pathwise_chain_survives": full_survival,
            "analytic_pathwise_gamma_lipschitz_proved": False,
            "analytic_pathwise_log_escape_lipschitz_proved": False,
            "cutoff_shell_uniform_authority": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "normalized_chord_path": "linear Fourier interpolation followed by target-packet-energy normalization",
            "path_length": "sum of physical Fourier coefficient L2 segment lengths",
            "gamma_local_loss": "positive Gamma increase along an oriented path segment",
            "log_escape_local_loss": "positive log escape decrease along an oriented path segment",
        },
        "parameters": {
            "search_cutoff": search_cutoff,
            "verify_cutoffs": list(verify_cutoffs),
            "target_shells": list(target_shells),
            "viscosity": nu,
            "target_packet_energy": target_packet_energy,
            "base_parameters": [asdict(parameter) for parameter in base_parameters],
            "center_seeds": list(center_seeds),
            "calibration_seeds": list(calibration_seeds),
            "holdout_seeds": list(holdout_seeds),
            "samples_per_base": samples_per_base,
            "gamma_threshold": gamma_threshold,
            "path_sample_count": path_sample_count,
            "modulus_slack": modulus_slack,
            "end_parabolic_time": end_parabolic_time,
            "output_count": output_count,
            "verify_count_per_shell": verify_count,
        },
        "center_profile_count": len(centers),
        "calibration_profile_count": len(calibration),
        "holdout_profile_count": len(holdout),
        "calibration_path_count": len(calibration_paths),
        "holdout_path_count": len(holdout_paths),
        "matched_profile_count": matched_profile_count,
        "matched_path_count": len(matched_paths),
        "fitted_path_constants": fitted,
        "holdout_evaluation": holdout_evaluation,
        "matched_evaluation": matched_evaluation,
        "matched_cutoff_groups": matched_groups,
        "maximum_matched_candidate_lower_spread": max(
            (group["candidate_lower_spread"] for group in matched_groups), default=None
        ),
        "maximum_matched_arc_length_spread": max(
            (group["arc_length_spread"] for group in matched_groups), default=None
        ),
        "maximum_mechanism_balance_residual": max(balance_residuals, default=None),
        "maximum_finite_difference_residual": max(fd_residuals, default=None),
        "maximum_path_normalization_residual": max(
            normalization_residuals, default=None
        ),
        "calibration_paths": calibration_paths,
        "holdout_paths": holdout_paths,
        "matched_paths": matched_paths,
        "centers": [strip_profile(profile) for profile in centers],
        "limitations": [
            "normalized chord paths are a selected finite path family",
            "segmentwise constants are fitted rather than analytically derived",
            "the path metric has not been proved cutoff uniform",
            "matched cutoffs do not establish continuum compactness",
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
    parser.add_argument("--phase-spreads", default="0.0,0.5")
    parser.add_argument("--target-ratios", default="1.25,2.5")
    parser.add_argument("--satellite-fractions", default="0.55")
    parser.add_argument("--center-seeds", default="1")
    parser.add_argument("--calibration-seeds", default="2")
    parser.add_argument("--holdout-seeds", default="3")
    parser.add_argument("--samples-per-base", type=int, default=2)
    parser.add_argument("--calibration-jitter-scale", type=float, default=1.0)
    parser.add_argument("--holdout-jitter-scale", type=float, default=1.0)
    parser.add_argument("--phase-jitter", type=float, default=0.8)
    parser.add_argument("--log-ratio-jitter", type=float, default=0.5)
    parser.add_argument("--log-satellite-jitter", type=float, default=0.35)
    parser.add_argument("--gamma-threshold", type=float, default=0.5)
    parser.add_argument("--path-sample-count", type=int, default=4)
    parser.add_argument("--modulus-slack", type=float, default=0.2)
    parser.add_argument("--end-parabolic-time", type=float, default=0.004)
    parser.add_argument("--output-count", type=int, default=3)
    parser.add_argument("--cfl", type=float, default=0.2)
    parser.add_argument("--verify-count", type=int, default=1)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    grid = packet_parameter_grid(
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
        base_parameters=grid,
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
        path_sample_count=args.path_sample_count,
        modulus_slack=args.modulus_slack,
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
                "gamma_lipschitz": result["fitted_path_constants"][
                    "fitted_gamma_lipschitz_constant"
                ],
                "log_escape_lipschitz": result["fitted_path_constants"][
                    "fitted_log_escape_lipschitz_constant"
                ],
                "holdout_lower": result["holdout_evaluation"][
                    "candidate_member_lower"
                ],
                "holdout_survives": result["authority"][
                    "sampled_pathwise_modulus_survives_holdout"
                ],
                "matched_survives": result["authority"][
                    "sampled_pathwise_modulus_survives_matched_cutoffs"
                ],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
