#!/usr/bin/env python3
"""Test a buffered Gamma modulus with multiplicative escape retention.

An additive escape allowance can destroy positivity when a finite-net radius is
large even though all sampled member escape supplies remain positive.  This
companion audit uses the logarithmic loss

    max(log E_center - log E_member, 0)

and fits

    log(E_center/E_member)_+ <= L_escape d^alpha.

Hence

    E_member >= exp(-L_escape d^alpha) E_center.

The Gamma buffer remains additive. Candidate Holder exponents are fitted on
calibration profiles, evaluated on held-out profiles, and rechecked on matched
N32/N48/N64 center/member pairs. The output is finite-Galerkin evidence only.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict
from pathlib import Path
from typing import Any

from ns_compact_gamma_common_u_net_audit import (
    PacketParameters,
    atomic_json,
    parse_float_tuple,
    parse_int_tuple,
    strip_profile,
)
from ns_compact_gamma_danger_expenditure_modulus_audit import (
    build_matched_pair_profiles,
    fit_holder_constant,
    matched_pairs,
    profile_center_pairs,
    select_adverse_members,
)
from ns_compact_gamma_remainder_oscillation_audit import build_split_profiles


def add_log_escape_loss(pairs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    enriched: list[dict[str, Any]] = []
    for pair in pairs:
        center = float(pair["center_escape"])
        member = float(pair["member_escape"])
        if center <= 0.0 or member <= 0.0:
            raise ValueError("multiplicative retention requires positive escape supplies")
        row = dict(pair)
        row["positive_log_escape_loss"] = max(math.log(center) - math.log(member), 0.0)
        enriched.append(row)
    return enriched


def evaluate_retained_candidate(
    *,
    exponent: float,
    gamma_constant: float,
    log_escape_constant: float,
    gamma_threshold: float,
    member_pairs: list[dict[str, Any]],
) -> dict[str, Any]:
    dangerous = [pair for pair in member_pairs if pair["member_dangerous"]]
    rows: list[dict[str, Any]] = []
    for pair in dangerous:
        distance_power = float(pair["distance"]) ** exponent
        gamma_allowance = gamma_constant * distance_power
        log_escape_allowance = log_escape_constant * distance_power
        retention_factor = math.exp(-log_escape_allowance)
        local_buffered_threshold = max(gamma_threshold - gamma_allowance, 0.0)
        local_member_lower = retention_factor * float(pair["center_escape"])
        gamma_margin = (
            float(pair["center_gamma"])
            + gamma_allowance
            - float(pair["member_gamma"])
        )
        retained_escape_margin = float(pair["member_escape"]) - local_member_lower
        buffered_center_margin = float(pair["center_gamma"]) - local_buffered_threshold
        rows.append(
            {
                **pair,
                "local_gamma_allowance": gamma_allowance,
                "local_log_escape_allowance": log_escape_allowance,
                "local_retention_factor": retention_factor,
                "local_buffered_threshold": local_buffered_threshold,
                "local_candidate_member_lower": local_member_lower,
                "gamma_modulus_margin": gamma_margin,
                "retained_escape_margin": retained_escape_margin,
                "buffered_center_margin": buffered_center_margin,
                "gamma_modulus_holds": gamma_margin >= -1.0e-10,
                "retained_escape_holds": retained_escape_margin >= -1.0e-10,
                "danger_transfers_to_buffered_center": buffered_center_margin >= -1.0e-10,
            }
        )
    family_lower = min(
        (row["local_candidate_member_lower"] for row in rows), default=None
    )
    survives = bool(rows) and family_lower is not None and family_lower > 0.0 and all(
        row["gamma_modulus_holds"]
        and row["retained_escape_holds"]
        and row["danger_transfers_to_buffered_center"]
        for row in rows
    )
    return {
        "exponent": exponent,
        "gamma_constant": gamma_constant,
        "log_escape_constant": log_escape_constant,
        "dangerous_pair_count": len(rows),
        "candidate_member_lower": family_lower,
        "positive_candidate_member_lower": family_lower is not None and family_lower > 0.0,
        "minimum_gamma_modulus_margin": min(
            (row["gamma_modulus_margin"] for row in rows), default=None
        ),
        "minimum_retained_escape_margin": min(
            (row["retained_escape_margin"] for row in rows), default=None
        ),
        "minimum_buffered_center_margin": min(
            (row["buffered_center_margin"] for row in rows), default=None
        ),
        "minimum_retention_factor": min(
            (row["local_retention_factor"] for row in rows), default=None
        ),
        "sampled_retained_danger_modulus_survives": survives,
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

    common = {
        "base_parameters": base_parameters,
        "samples_per_base": samples_per_base,
        "phase_jitter": phase_jitter,
        "log_ratio_jitter": log_ratio_jitter,
        "log_satellite_jitter": log_satellite_jitter,
        "cutoff": search_cutoff,
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
        **{key: value for key, value in common.items() if key not in {
            "phase_jitter", "log_ratio_jitter", "log_satellite_jitter"
        }},
    )
    holdout = build_split_profiles(
        split="holdout",
        seeds=holdout_seeds,
        perturb=True,
        phase_jitter=holdout_jitter_scale * phase_jitter,
        log_ratio_jitter=holdout_jitter_scale * log_ratio_jitter,
        log_satellite_jitter=holdout_jitter_scale * log_satellite_jitter,
        **{key: value for key, value in common.items() if key not in {
            "phase_jitter", "log_ratio_jitter", "log_satellite_jitter"
        }},
    )

    calibration_pairs = add_log_escape_loss(profile_center_pairs(calibration, centers))
    holdout_pairs = add_log_escape_loss(profile_center_pairs(holdout, centers))
    candidates: list[dict[str, Any]] = []
    for exponent in sorted(set(holder_exponents), reverse=True):
        gamma_fit = fit_holder_constant(
            calibration_pairs,
            exponent=exponent,
            field="positive_gamma_loss",
            slack=modulus_slack,
        )
        log_escape_fit = fit_holder_constant(
            calibration_pairs,
            exponent=exponent,
            field="positive_log_escape_loss",
            slack=modulus_slack,
        )
        evaluation = evaluate_retained_candidate(
            exponent=exponent,
            gamma_constant=float(gamma_fit["fitted_constant"]),
            log_escape_constant=float(log_escape_fit["fitted_constant"]),
            gamma_threshold=gamma_threshold,
            member_pairs=holdout_pairs,
        )
        candidates.append(
            {
                "exponent": exponent,
                "gamma_fit": gamma_fit,
                "log_escape_fit": log_escape_fit,
                "holdout_evaluation": evaluation,
            }
        )

    surviving = [
        candidate
        for candidate in candidates
        if candidate["holdout_evaluation"][
            "sampled_retained_danger_modulus_survives"
        ]
    ]
    selected = surviving[0] if surviving else candidates[-1]

    adverse_members = select_adverse_members(holdout, verify_count)
    matched_profiles = build_matched_pair_profiles(
        selected_members=adverse_members,
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
    matched_pair_rows = add_log_escape_loss(matched_pairs(matched_profiles))
    matched_evaluation = evaluate_retained_candidate(
        exponent=float(selected["exponent"]),
        gamma_constant=float(selected["gamma_fit"]["fitted_constant"]),
        log_escape_constant=float(selected["log_escape_fit"]["fitted_constant"]),
        gamma_threshold=gamma_threshold,
        member_pairs=matched_pair_rows,
    )

    group_map: dict[tuple[int, float], list[dict[str, Any]]] = {}
    for row in matched_evaluation["rows"]:
        group_map.setdefault(
            (int(row["target_shell"]), float(row["parabolic_time"])), []
        ).append(row)
    matched_groups: list[dict[str, Any]] = []
    for (shell, time), rows in sorted(group_map.items()):
        cutoffs = sorted({int(row["cutoff"]) for row in rows})
        lowers = [float(row["local_candidate_member_lower"]) for row in rows]
        escapes = [float(row["member_escape"]) for row in rows]
        matched_groups.append(
            {
                "target_shell": shell,
                "parabolic_time": time,
                "observed_cutoffs": cutoffs,
                "matched_cutoff_complete": set(cutoffs) == set(verify_cutoffs),
                "candidate_lower_spread": max(lowers) - min(lowers),
                "member_escape_spread": max(escapes) - min(escapes),
                "all_rows_retained": all(row["retained_escape_holds"] for row in rows),
            }
        )

    all_rows = [row for profile in centers + calibration + holdout for row in profile["rows"]]
    all_rows += [
        row
        for item in matched_profiles
        for profile_key in ("member_profile", "center_profile")
        for row in item[profile_key]["rows"]
    ]
    divergence = [
        float(row["angular_packet_metrics"]["relative_divergence_residual"])
        for row in all_rows
    ]
    balance = [
        float(row["mechanism_accounting"]["mechanism_balance_residual"])
        for row in all_rows
        if row["mechanism_accounting"] is not None
    ]
    finite_difference = [
        float(row["finite_difference_residual"])
        for row in all_rows
        if row["finite_difference_residual"] is not None
    ]

    holdout_survives = bool(
        selected["holdout_evaluation"]["sampled_retained_danger_modulus_survives"]
    )
    matched_survives = bool(
        matched_evaluation["sampled_retained_danger_modulus_survives"]
    ) and all(group["matched_cutoff_complete"] for group in matched_groups)
    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_retained_danger_audit": True,
            "sampled_retained_modulus_survives_holdout": holdout_survives,
            "sampled_retained_modulus_survives_matched_cutoffs": matched_survives,
            "analytic_gamma_modulus_proved": False,
            "analytic_log_escape_modulus_proved": False,
            "cutoff_shell_uniform_authority": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "positive_log_escape_loss": "max(log(center escape)-log(member escape),0)",
            "retention_factor": "exp(-L_escape d^alpha)",
            "candidate_member_lower": "retention factor times paired center escape",
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
            "holder_exponents": list(holder_exponents),
            "modulus_slack": modulus_slack,
            "end_parabolic_time": end_parabolic_time,
            "output_count": output_count,
        },
        "center_profile_count": len(centers),
        "calibration_profile_count": len(calibration),
        "holdout_profile_count": len(holdout),
        "calibration_pair_count": len(calibration_pairs),
        "holdout_pair_count": len(holdout_pairs),
        "candidate_moduli": candidates,
        "surviving_candidate_count": len(surviving),
        "selected_candidate": selected,
        "selected_holdout_evaluation": selected["holdout_evaluation"],
        "matched_profile_pair_count": len(matched_profiles),
        "matched_pair_row_count": len(matched_pair_rows),
        "matched_evaluation": matched_evaluation,
        "matched_cutoff_groups": matched_groups,
        "maximum_matched_candidate_lower_spread": max(
            (group["candidate_lower_spread"] for group in matched_groups), default=None
        ),
        "maximum_matched_escape_spread": max(
            (group["member_escape_spread"] for group in matched_groups), default=None
        ),
        "maximum_relative_divergence_residual": max(divergence, default=None),
        "maximum_mechanism_balance_residual": max(balance, default=None),
        "maximum_finite_difference_residual": max(finite_difference, default=None),
        "centers": [strip_profile(profile) for profile in centers],
        "calibration_profiles": [strip_profile(profile) for profile in calibration],
        "holdout_profiles": [strip_profile(profile) for profile in holdout],
        "limitations": [
            "logarithmic Holder constants are fitted from finite calibration profiles",
            "paired center escape is sampled rather than bounded analytically",
            "matched cutoffs do not establish a continuum modulus",
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
    parser.add_argument("--samples-per-base", type=int, default=4)
    parser.add_argument("--calibration-jitter-scale", type=float, default=1.0)
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

    base_parameters = PacketParameters
    from ns_compact_gamma_common_u_net_audit import packet_parameter_grid

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
        holder_exponents=parse_float_tuple(args.holder_exponents),
        modulus_slack=args.modulus_slack,
        end_parabolic_time=args.end_parabolic_time,
        output_count=args.output_count,
        cfl=args.cfl,
        verify_count=args.verify_count,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "surviving_candidate_count": result["surviving_candidate_count"],
        "selected_exponent": result["selected_candidate"]["exponent"],
        "candidate_member_lower": result["selected_holdout_evaluation"]["candidate_member_lower"],
        "holdout_survives": result["authority"]["sampled_retained_modulus_survives_holdout"],
        "matched_survives": result["authority"]["sampled_retained_modulus_survives_matched_cutoffs"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
