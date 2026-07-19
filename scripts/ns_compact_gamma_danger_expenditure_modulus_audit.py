#!/usr/bin/env python3
"""Search for a buffered finite-net lower bound on compact-Gamma expenditure.

The remainder-oscillation audit found that a center-fitted positive lower bound
on the escape supply E_K did not survive normalized profile perturbations.  This
lane tests the correct finite-net statement.

For a member state u and a nearby center v, fit one-sided Holder moduli

    Gamma(u) - Gamma(v) <= L_gamma d(u,v)^alpha,
    E(v) - E(u)         <= L_escape d(u,v)^alpha.

Thus member danger Gamma(u) >= lambda transfers to the buffered center level

    Gamma(v) >= lambda - delta_gamma.

If centers above that buffered level satisfy E(v) >= c_center, then

    E(u) >= c_center - delta_escape =: c_member.

The script fits candidate exponents on calibration profiles, checks them on
held-out profiles, and rechecks the most adverse held-out states at matched
N32/N48/N64 cutoffs.  All output is finite-Galerkin evidence only.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict
from pathlib import Path
from typing import Any, Iterable

import numpy as np

from ns_compact_gamma_common_u_net_audit import (
    PacketParameters,
    atomic_json,
    build_profile,
    mechanism_rates,
    nearest_center,
    packet_parameter_grid,
    parse_float_tuple,
    parse_int_tuple,
    strip_profile,
)
from ns_compact_gamma_remainder_oscillation_audit import build_split_profiles


def row_at_time(profile: dict[str, Any], parabolic_time: float) -> dict[str, Any]:
    matches = [
        row
        for row in profile["rows"]
        if math.isclose(
            float(row["parabolic_time"]), parabolic_time, rel_tol=0.0, abs_tol=1.0e-12
        )
    ]
    if len(matches) != 1:
        raise ValueError(
            f"expected one row at tau={parabolic_time} for {profile['profile_id']}"
        )
    return matches[0]


def profile_center_pairs(
    profiles: Iterable[dict[str, Any]], centers: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    pairs: list[dict[str, Any]] = []
    for profile in profiles:
        center, distance = nearest_center(profile, centers)
        for member_row in profile["rows"]:
            time = float(member_row["parabolic_time"])
            center_row = row_at_time(center, time)
            member_escape, _member_replenishment = mechanism_rates(member_row)
            center_escape, _center_replenishment = mechanism_rates(center_row)
            member_gamma = float(member_row["gamma"])
            center_gamma = float(center_row["gamma"])
            pairs.append(
                {
                    "profile_id": profile["profile_id"],
                    "center_profile_id": center["profile_id"],
                    "target_shell": int(profile["target_shell"]),
                    "triad_count": int(profile["parameters"]["triad_count"]),
                    "parabolic_time": time,
                    "distance": float(distance),
                    "member_gamma": member_gamma,
                    "center_gamma": center_gamma,
                    "positive_gamma_loss": max(member_gamma - center_gamma, 0.0),
                    "member_escape": member_escape,
                    "center_escape": center_escape,
                    "positive_escape_loss": max(center_escape - member_escape, 0.0),
                    "member_dangerous": bool(member_row["dangerous"]),
                    "center_dangerous": bool(center_row["dangerous"]),
                }
            )
    return pairs


def fit_holder_constant(
    pairs: list[dict[str, Any]],
    *,
    exponent: float,
    field: str,
    slack: float,
) -> dict[str, Any]:
    if not 0.0 < exponent <= 1.0:
        raise ValueError("Holder exponent must lie in (0,1]")
    if not math.isfinite(slack) or slack < 0.0:
        raise ValueError("modulus slack must be finite and nonnegative")
    samples: list[dict[str, Any]] = []
    constants: list[float] = []
    singular = False
    for pair in pairs:
        distance = float(pair["distance"])
        loss = float(pair[field])
        denominator = distance ** exponent
        if denominator <= 1.0e-14:
            observed = 0.0 if loss <= 1.0e-12 else math.inf
        else:
            observed = loss / denominator
        if math.isfinite(observed):
            constants.append(observed)
        else:
            singular = True
        samples.append(
            {
                "profile_id": pair["profile_id"],
                "center_profile_id": pair["center_profile_id"],
                "parabolic_time": pair["parabolic_time"],
                "distance": distance,
                "loss": loss,
                "observed_constant": observed,
            }
        )
    raw = math.inf if singular else max(constants, default=0.0)
    fitted = math.inf if not math.isfinite(raw) else raw * (1.0 + slack)
    return {
        "exponent": exponent,
        "field": field,
        "raw_constant": raw,
        "fitted_constant": fitted,
        "singular_zero_distance_loss": singular,
        "sample_count": len(samples),
        "samples": samples,
    }


def center_escape_lower(
    centers: list[dict[str, Any]], buffered_threshold: float
) -> dict[str, Any]:
    eligible: list[dict[str, Any]] = []
    for center in centers:
        for row in center["rows"]:
            gamma = float(row["gamma"])
            if gamma + 1.0e-12 < buffered_threshold:
                continue
            escape, _replenishment = mechanism_rates(row)
            eligible.append(
                {
                    "profile_id": center["profile_id"],
                    "target_shell": int(center["target_shell"]),
                    "parabolic_time": float(row["parabolic_time"]),
                    "gamma": gamma,
                    "escape_supply": escape,
                }
            )
    return {
        "buffered_threshold": buffered_threshold,
        "eligible_center_row_count": len(eligible),
        "center_escape_lower": min(
            (row["escape_supply"] for row in eligible), default=None
        ),
        "eligible_rows": eligible,
    }


def evaluate_candidate(
    *,
    exponent: float,
    gamma_constant: float,
    escape_constant: float,
    gamma_threshold: float,
    centers: list[dict[str, Any]],
    member_pairs: list[dict[str, Any]],
) -> dict[str, Any]:
    dangerous_pairs = [pair for pair in member_pairs if pair["member_dangerous"]]
    coverage_radius = max((float(pair["distance"]) for pair in member_pairs), default=0.0)
    gamma_allowance = gamma_constant * coverage_radius ** exponent
    escape_allowance = escape_constant * coverage_radius ** exponent
    buffered_threshold = max(gamma_threshold - gamma_allowance, 0.0)
    center_lower_receipt = center_escape_lower(centers, buffered_threshold)
    c_center = center_lower_receipt["center_escape_lower"]
    c_member = None if c_center is None else float(c_center) - escape_allowance

    rows: list[dict[str, Any]] = []
    for pair in dangerous_pairs:
        distance_power = float(pair["distance"]) ** exponent
        local_gamma_allowance = gamma_constant * distance_power
        local_escape_allowance = escape_constant * distance_power
        gamma_margin = (
            float(pair["center_gamma"])
            + local_gamma_allowance
            - float(pair["member_gamma"])
        )
        escape_loss_margin = (
            float(pair["member_escape"])
            + local_escape_allowance
            - float(pair["center_escape"])
        )
        buffered_center_margin = float(pair["center_gamma"]) - buffered_threshold
        member_lower_margin = (
            None if c_member is None else float(pair["member_escape"]) - c_member
        )
        rows.append(
            {
                **pair,
                "local_gamma_allowance": local_gamma_allowance,
                "local_escape_allowance": local_escape_allowance,
                "gamma_modulus_margin": gamma_margin,
                "escape_modulus_margin": escape_loss_margin,
                "buffered_center_margin": buffered_center_margin,
                "candidate_member_lower_margin": member_lower_margin,
                "gamma_modulus_holds": gamma_margin >= -1.0e-10,
                "escape_modulus_holds": escape_loss_margin >= -1.0e-10,
                "danger_transfers_to_buffered_center": buffered_center_margin >= -1.0e-10,
                "candidate_member_lower_holds": (
                    member_lower_margin is not None and member_lower_margin >= -1.0e-10
                ),
            }
        )

    positive_member_lower = c_member is not None and c_member > 0.0
    all_rows_hold = bool(rows) and all(
        row["gamma_modulus_holds"]
        and row["escape_modulus_holds"]
        and row["danger_transfers_to_buffered_center"]
        and row["candidate_member_lower_holds"]
        for row in rows
    )
    return {
        "exponent": exponent,
        "gamma_constant": gamma_constant,
        "escape_constant": escape_constant,
        "coverage_radius": coverage_radius,
        "gamma_allowance": gamma_allowance,
        "escape_allowance": escape_allowance,
        "buffered_center_threshold": buffered_threshold,
        "center_lower_receipt": center_lower_receipt,
        "candidate_member_lower": c_member,
        "positive_candidate_member_lower": positive_member_lower,
        "dangerous_pair_count": len(rows),
        "rows": rows,
        "minimum_gamma_modulus_margin": min(
            (row["gamma_modulus_margin"] for row in rows), default=None
        ),
        "minimum_escape_modulus_margin": min(
            (row["escape_modulus_margin"] for row in rows), default=None
        ),
        "minimum_buffered_center_margin": min(
            (row["buffered_center_margin"] for row in rows), default=None
        ),
        "minimum_member_lower_margin": min(
            (
                row["candidate_member_lower_margin"]
                for row in rows
                if row["candidate_member_lower_margin"] is not None
            ),
            default=None,
        ),
        "sampled_buffered_danger_modulus_survives": positive_member_lower
        and all_rows_hold,
    }


def build_matched_pair_profiles(
    *,
    selected_members: list[dict[str, Any]],
    centers: list[dict[str, Any]],
    verify_cutoffs: tuple[int, ...],
    nu: float,
    input_amplitude: float,
    target_packet_energy: float,
    gamma_threshold: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
) -> list[dict[str, Any]]:
    matched: list[dict[str, Any]] = []
    for member in selected_members:
        center, _distance = nearest_center(member, centers)
        member_parameters = PacketParameters(**member["parameters"])
        center_parameters = PacketParameters(**center["parameters"])
        shell = int(member["target_shell"])
        for cutoff in verify_cutoffs:
            member_profile = build_profile(
                split="matched-member",
                seed=int(member["derived_state_seed"]),
                parameters=member_parameters,
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
            center_profile = build_profile(
                split="matched-center",
                seed=int(center["derived_state_seed"]),
                parameters=center_parameters,
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
            matched.append(
                {
                    "cutoff": cutoff,
                    "target_shell": shell,
                    "source_member_profile_id": member["profile_id"],
                    "source_center_profile_id": center["profile_id"],
                    "member_profile": member_profile,
                    "center_profile": center_profile,
                }
            )
    return matched


def matched_pairs(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for item in rows:
        member = item["member_profile"]
        center = item["center_profile"]
        distance = float(np.linalg.norm(member["feature"] - center["feature"]))
        for member_row in member["rows"]:
            time = float(member_row["parabolic_time"])
            center_row = row_at_time(center, time)
            member_escape, _ = mechanism_rates(member_row)
            center_escape, _ = mechanism_rates(center_row)
            member_gamma = float(member_row["gamma"])
            center_gamma = float(center_row["gamma"])
            output.append(
                {
                    "profile_id": member["profile_id"],
                    "center_profile_id": center["profile_id"],
                    "cutoff": int(item["cutoff"]),
                    "target_shell": int(item["target_shell"]),
                    "triad_count": int(member["parameters"]["triad_count"]),
                    "parabolic_time": time,
                    "distance": distance,
                    "member_gamma": member_gamma,
                    "center_gamma": center_gamma,
                    "positive_gamma_loss": max(member_gamma - center_gamma, 0.0),
                    "member_escape": member_escape,
                    "center_escape": center_escape,
                    "positive_escape_loss": max(center_escape - member_escape, 0.0),
                    "member_dangerous": bool(member_row["dangerous"]),
                    "center_dangerous": bool(center_row["dangerous"]),
                }
            )
    return output


def select_adverse_members(
    holdout: list[dict[str, Any]], verify_count: int
) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    shells = sorted({int(profile["target_shell"]) for profile in holdout})
    for shell in shells:
        candidates = [profile for profile in holdout if int(profile["target_shell"]) == shell]

        def key(profile: dict[str, Any]) -> tuple[float, float]:
            dangerous_escapes = [
                mechanism_rates(row)[0]
                for row in profile["rows"]
                if bool(row["dangerous"])
            ]
            minimum_escape = min(dangerous_escapes, default=math.inf)
            maximum_gamma = max(float(row["gamma"]) for row in profile["rows"])
            return minimum_escape, -maximum_gamma

        selected.extend(sorted(candidates, key=key)[:verify_count])
    return selected


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
    holder_exponents: tuple[float, ...],
    modulus_slack: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
    verify_count: int,
) -> dict[str, Any]:
    all_seeds = center_seeds + calibration_seeds + holdout_seeds
    if len(all_seeds) != len(set(all_seeds)):
        raise ValueError("center, calibration, and holdout seeds must be disjoint")
    if not holder_exponents:
        raise ValueError("at least one Holder exponent is required")

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

    calibration_pairs = profile_center_pairs(calibration, centers)
    holdout_pairs = profile_center_pairs(holdout, centers)
    candidates: list[dict[str, Any]] = []
    for exponent in sorted(set(holder_exponents), reverse=True):
        gamma_fit = fit_holder_constant(
            calibration_pairs,
            exponent=exponent,
            field="positive_gamma_loss",
            slack=modulus_slack,
        )
        escape_fit = fit_holder_constant(
            calibration_pairs,
            exponent=exponent,
            field="positive_escape_loss",
            slack=modulus_slack,
        )
        evaluation = evaluate_candidate(
            exponent=exponent,
            gamma_constant=float(gamma_fit["fitted_constant"]),
            escape_constant=float(escape_fit["fitted_constant"]),
            gamma_threshold=gamma_threshold,
            centers=centers,
            member_pairs=holdout_pairs,
        )
        candidates.append(
            {
                "exponent": exponent,
                "gamma_fit": gamma_fit,
                "escape_fit": escape_fit,
                "holdout_evaluation": evaluation,
            }
        )

    surviving = [
        candidate
        for candidate in candidates
        if candidate["holdout_evaluation"][
            "sampled_buffered_danger_modulus_survives"
        ]
    ]
    selected_candidate = surviving[0] if surviving else candidates[-1]
    selected_evaluation = selected_candidate["holdout_evaluation"]

    selected_members = select_adverse_members(holdout, verify_count)
    matched_profiles = build_matched_pair_profiles(
        selected_members=selected_members,
        centers=centers,
        verify_cutoffs=verify_cutoffs,
        nu=nu,
        input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    matched_pair_rows = matched_pairs(matched_profiles)
    matched_evaluation = evaluate_candidate(
        exponent=float(selected_candidate["exponent"]),
        gamma_constant=float(selected_candidate["gamma_fit"]["fitted_constant"]),
        escape_constant=float(selected_candidate["escape_fit"]["fitted_constant"]),
        gamma_threshold=gamma_threshold,
        centers=centers,
        member_pairs=matched_pair_rows,
    )

    group_map: dict[tuple[int, float], list[dict[str, Any]]] = {}
    for row in matched_evaluation["rows"]:
        key = (int(row["target_shell"]), float(row["parabolic_time"]))
        group_map.setdefault(key, []).append(row)
    matched_groups: list[dict[str, Any]] = []
    for (shell, time), rows in sorted(group_map.items()):
        cutoffs = sorted({int(row["cutoff"]) for row in rows})
        escapes = [float(row["member_escape"]) for row in rows]
        gammas = [float(row["member_gamma"]) for row in rows]
        matched_groups.append(
            {
                "target_shell": shell,
                "parabolic_time": time,
                "observed_cutoffs": cutoffs,
                "matched_cutoff_complete": set(cutoffs) == set(verify_cutoffs),
                "member_escape_spread": max(escapes) - min(escapes),
                "member_gamma_spread": max(gammas) - min(gammas),
                "all_rows_meet_candidate_lower": all(
                    row["candidate_member_lower_holds"] for row in rows
                ),
            }
        )

    all_profiles = centers + calibration + holdout
    all_rows = [
        row
        for profile in all_profiles
        for row in profile["rows"]
    ] + [
        row
        for item in matched_profiles
        for profile_key in ("member_profile", "center_profile")
        for row in item[profile_key]["rows"]
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

    selected_survives_holdout = bool(
        selected_evaluation["sampled_buffered_danger_modulus_survives"]
    )
    selected_survives_matched = bool(
        matched_evaluation["sampled_buffered_danger_modulus_survives"]
    ) and all(group["matched_cutoff_complete"] for group in matched_groups)
    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_buffered_danger_audit": True,
            "holder_modulus_candidates_tested": True,
            "sampled_modulus_survives_holdout": selected_survives_holdout,
            "sampled_modulus_survives_matched_cutoffs": selected_survives_matched,
            "analytic_gamma_modulus_proved": False,
            "analytic_escape_modulus_proved": False,
            "cutoff_shell_uniform_authority": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "gamma_modulus": "positive member-minus-center Gamma loss",
            "escape_modulus": "positive center-minus-member escape loss",
            "buffered_center_threshold": "lambda minus the global finite-net Gamma allowance",
            "candidate_member_lower": "buffered center escape lower minus escape allowance",
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
            "holder_exponents": list(holder_exponents),
            "modulus_slack": modulus_slack,
            "end_parabolic_time": end_parabolic_time,
            "output_count": output_count,
            "cfl": cfl,
            "verify_count_per_shell": verify_count,
        },
        "center_profile_count": len(centers),
        "calibration_profile_count": len(calibration),
        "holdout_profile_count": len(holdout),
        "calibration_pair_count": len(calibration_pairs),
        "holdout_pair_count": len(holdout_pairs),
        "candidate_moduli": candidates,
        "surviving_candidate_count": len(surviving),
        "selected_candidate": selected_candidate,
        "selected_holdout_evaluation": selected_evaluation,
        "selected_member_profile_count": len(selected_members),
        "matched_profile_pair_count": len(matched_profiles),
        "matched_pair_row_count": len(matched_pair_rows),
        "matched_evaluation": matched_evaluation,
        "matched_cutoff_groups": matched_groups,
        "maximum_matched_escape_spread": max(
            (group["member_escape_spread"] for group in matched_groups), default=None
        ),
        "maximum_matched_gamma_spread": max(
            (group["member_gamma_spread"] for group in matched_groups), default=None
        ),
        "maximum_relative_divergence_residual": max(divergence_residuals, default=None),
        "maximum_mechanism_balance_residual": max(mechanism_residuals, default=None),
        "maximum_finite_difference_residual": max(fd_residuals, default=None),
        "centers": [strip_profile(profile) for profile in centers],
        "calibration_profiles": [strip_profile(profile) for profile in calibration],
        "holdout_profiles": [strip_profile(profile) for profile in holdout],
        "matched_profiles": [
            {
                "cutoff": item["cutoff"],
                "target_shell": item["target_shell"],
                "source_member_profile_id": item["source_member_profile_id"],
                "source_center_profile_id": item["source_center_profile_id"],
                "member_profile": strip_profile(item["member_profile"]),
                "center_profile": strip_profile(item["center_profile"]),
            }
            for item in matched_profiles
        ],
        "limitations": [
            "candidate Holder constants are fitted from finite calibration profiles",
            "held-out success does not prove an analytic modulus",
            "the buffered center lower is sampled rather than derived from PDE estimates",
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
    parser.add_argument("--holder-exponents", default="1.0,0.75,0.5,0.25")
    parser.add_argument("--modulus-slack", type=float, default=0.15)
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
        holder_exponents=parse_float_tuple(args.holder_exponents),
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
                "surviving_candidate_count": result["surviving_candidate_count"],
                "selected_exponent": result["selected_candidate"]["exponent"],
                "candidate_member_lower": result["selected_holdout_evaluation"][
                    "candidate_member_lower"
                ],
                "holdout_survives": result["authority"][
                    "sampled_modulus_survives_holdout"
                ],
                "matched_survives": result["authority"][
                    "sampled_modulus_survives_matched_cutoffs"
                ],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
