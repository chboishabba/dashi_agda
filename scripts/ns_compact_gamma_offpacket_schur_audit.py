#!/usr/bin/env python3
"""Audit shell/angular weighted control of the compact-Gamma off-packet derivative.

The exact differential lane localized the held-out failure of a common
``D log E`` modulus to

    D m_off(u)[h],

where ``m_off`` is the off-packet nonlinear contribution to the parabolically
normalized derivative of the bounded compact-Gamma potential.  This script
keeps that derivative exact at finite Galerkin cutoff and asks whether the
failure is repaired by a declared shell/angular tangent norm plus an explicit
far-shell tail:

    |D m_off(u)[h]|
      <= C_Schur E(u) ||h||_{X~_{K,sigma,eta}} + Tail_{K,r}(u,h).

The weighted norm is

    ||h||^2 = sum_k (1 + 2^(-2K)|k|^2)
                    2^(2 sigma |j(k)-K|)
                    (1 + eta a_K(k))^2 |h_k|^2,

where ``j(k)=floor(log2 |k|)`` and ``a_K(k)`` is the projective angular defect
relative to the target-packet Fourier second moment.  The tangent is projected
onto the fixed target-packet-energy surface before the split.  Shell pieces
are reality closed and their exact signed derivatives are checked to
reconstruct the full derivative.

Constants are fitted on calibration states, then applied unchanged to an
independent held-out family and exact-seed matched N32/N48/N64 states.  This is
finite-Galerkin proof search.  It does not prove a Schur estimate, tail
absorption, shell/cutoff uniformity, compactness, BKM continuation, or Clay
regularity.
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
    nearest_center,
    packet_parameter_grid,
    parse_float_tuple,
    parse_int_tuple,
)
from ns_compact_gamma_differential_modulus_audit import (
    compact_second,
    dangerous_rows,
    inner_hat,
    mechanism_fields,
    path_state_tangent,
    prepare,
    project_energy_tangent,
)
from ns_compact_gamma_pathwise_retention_audit import (
    build_profile_sets,
    reconstruct_trajectory,
    state_at_time,
)
from ns_compact_gamma_potential_audit import (
    _directional_derivative,
    _state_geometry,
    compact_gamma_snapshot,
)
from ns_compact_gamma_replenishment_audit import mechanism_accounting


OFF_MECHANISM = "off_packet_nonlinear"


def shell_index(norm: np.ndarray) -> np.ndarray:
    """Return the dyadic shell index, with a sentinel at the zero mode."""
    result = np.full(norm.shape, -10_000, dtype=np.int64)
    positive = norm > 0.0
    result[positive] = np.floor(np.log2(norm[positive]) + 1.0e-12).astype(np.int64)
    return result


def projective_angular_bin(wave: np.ndarray) -> np.ndarray:
    """Reality-invariant six-sector bin from the two dominant coordinate axes."""
    order = np.argsort(-np.abs(wave), axis=-1, kind="stable")
    return order[..., 0] * 3 + order[..., 1]


def packet_orientation(values: dict[str, Any]) -> tuple[np.ndarray, np.ndarray]:
    """Target-packet second moment and projective angular defect per mode."""
    geometry = values["geometry"]
    n = int(geometry["cutoff"])
    packet = geometry["packet"]
    wave = geometry["wave"]
    norm_sq = geometry["norm_sq"]
    field = geometry["packet_hat"] / float(n ** 3)
    modal_energy = np.sum(np.abs(field) ** 2, axis=-1)
    total = float(np.sum(modal_energy[packet]))
    if total <= 1.0e-30:
        raise ValueError("target packet has zero energy")
    unit = np.divide(
        wave,
        np.sqrt(norm_sq)[..., None],
        out=np.zeros_like(wave, dtype=np.float64),
        where=norm_sq[..., None] > 0.0,
    )
    moment = np.einsum(
        "...,...i,...j->ij",
        modal_energy * packet,
        unit,
        unit,
    ) / total
    defect = 1.0 - np.einsum("...i,ij,...j->...", unit, moment, unit)
    defect = np.clip(defect, 0.0, 1.0)
    return moment, defect


def off_packet_derivative(
    values: dict[str, Any], tangent: np.ndarray, *, nu: float, shell: int
) -> float:
    """Exact finite-Galerkin derivative of the signed off-packet mechanism."""
    fields = mechanism_fields(values, None, nu)
    dfields = mechanism_fields(values, tangent, nu)
    second = compact_second(values, tangent, fields[OFF_MECHANISM], nu, shell)
    field_dot = _directional_derivative(
        values, dfields[OFF_MECHANISM], nu, shell
    )["compact_gamma_potential_derivative"]
    if field_dot is None:
        raise ValueError("off-packet field derivative hit the compact-Gamma kink")
    return (second + float(field_dot)) / float(values["parabolic_rate"])


def xk_density(values: dict[str, Any], tangent: np.ndarray, shell: int) -> np.ndarray:
    geometry = values["geometry"]
    n = int(geometry["cutoff"])
    physical = tangent / float(n ** 3)
    modal = np.sum(np.abs(physical) ** 2, axis=-1)
    return modal * (1.0 + float(2 ** (-2 * shell)) * geometry["norm_sq"])


def weighted_norm_from_components(
    shell_components: list[dict[str, Any]], *, shell_exponent: float, angular_eta: float
) -> float:
    square = 0.0
    for component in shell_components:
        offset = abs(int(component["shell_offset"]))
        radial = float(2.0 ** (2.0 * shell_exponent * offset))
        e0 = float(component["xk_energy"])
        e1 = float(component["xk_angular_moment_1"])
        e2 = float(component["xk_angular_moment_2"])
        square += radial * (e0 + 2.0 * angular_eta * e1 + angular_eta * angular_eta * e2)
    return math.sqrt(max(square, 0.0))


def candidate_metrics(
    row: dict[str, Any], *, shell_exponent: float, angular_eta: float, tail_radius: int
) -> dict[str, float]:
    weighted_norm = weighted_norm_from_components(
        row["shell_components"],
        shell_exponent=shell_exponent,
        angular_eta=angular_eta,
    )
    if weighted_norm <= 1.0e-30:
        raise ValueError("weighted tangent norm vanished")
    escape = float(row["escape_supply"])
    if escape <= 1.0e-30:
        raise ValueError("escape supply vanished")
    near = sum(
        abs(float(component["off_derivative_contribution"]))
        for component in row["shell_components"]
        if abs(int(component["shell_offset"])) <= tail_radius
    )
    tail = sum(
        abs(float(component["off_derivative_contribution"]))
        for component in row["shell_components"]
        if abs(int(component["shell_offset"])) > tail_radius
    )
    full = abs(float(row["off_derivative"]))
    denominator = escape * weighted_norm
    return {
        "weighted_norm": weighted_norm,
        "near_absolute_response": near,
        "tail_absolute_response": tail,
        "full_absolute_response": full,
        "near_schur_quotient": near / denominator,
        "tail_quotient": tail / denominator,
        "full_quotient": full / denominator,
        "tail_over_full_response": tail / max(full, 1.0e-30),
    }


def off_response(
    raw: np.ndarray,
    tangent: np.ndarray,
    *,
    nu: float,
    shell: int,
    finite_difference_relative_step: float = 2.0e-7,
) -> dict[str, Any]:
    snapshot = compact_gamma_snapshot(raw, nu, shell)
    if snapshot["positive_part_branch"] != "strict_positive_transfer":
        return {
            "resolved": False,
            "reason": "positive-transfer-branch",
            "gamma": float(snapshot["gamma"]),
        }
    values = {**snapshot, "geometry": _state_geometry(raw, nu, shell)}
    tangent, tangent_residual = project_energy_tangent(values, tangent)
    tangent = prepare(values, tangent)
    base_density = xk_density(values, tangent, shell)
    base_norm = math.sqrt(max(float(np.sum(base_density)), 0.0))
    if base_norm <= 1.0e-30:
        return {
            "resolved": False,
            "reason": "zero-projected-tangent",
            "gamma": float(snapshot["gamma"]),
        }

    accounting = mechanism_accounting(snapshot)
    escape = float(accounting["escape_supply"])
    if escape <= 1.0e-30:
        return {
            "resolved": False,
            "reason": "zero-escape",
            "gamma": float(snapshot["gamma"]),
        }

    full_derivative = off_packet_derivative(values, tangent, nu=nu, shell=shell)
    orientation, angular_defect = packet_orientation(values)
    geometry = values["geometry"]
    retained = geometry["dealias"] & (geometry["norm_sq"] > 0.0)
    indices = shell_index(np.sqrt(geometry["norm_sq"]))
    angular_bins = projective_angular_bin(geometry["wave"])

    shell_components: list[dict[str, Any]] = []
    angular_rows: list[dict[str, Any]] = []
    active_offsets = sorted({
        int(index - shell)
        for index in indices[retained & (base_density > 1.0e-32)]
    })
    for offset in active_offsets:
        mask = retained & (indices == shell + offset)
        component = tangent * mask[..., None]
        derivative = off_packet_derivative(values, component, nu=nu, shell=shell)
        density = base_density * mask
        shell_components.append({
            "shell_offset": offset,
            "mode_count": int(np.count_nonzero(mask)),
            "off_derivative_contribution": derivative,
            "xk_energy": float(np.sum(density)),
            "xk_angular_moment_1": float(np.sum(density * angular_defect)),
            "xk_angular_moment_2": float(np.sum(density * angular_defect * angular_defect)),
        })
        for angular_bin in sorted({int(value) for value in angular_bins[mask]}):
            local = mask & (angular_bins == angular_bin)
            angular_rows.append({
                "shell_offset": offset,
                "angular_bin": angular_bin,
                "mode_count": int(np.count_nonzero(local)),
                "xk_energy": float(np.sum(base_density * local)),
                "mean_projective_angular_defect": (
                    float(np.sum(base_density * local * angular_defect))
                    / max(float(np.sum(base_density * local)), 1.0e-30)
                ),
            })

    reconstruction = abs(
        sum(float(component["off_derivative_contribution"]) for component in shell_components)
        - full_derivative
    )
    density_reconstruction = abs(
        sum(float(component["xk_energy"]) for component in shell_components)
        - base_norm * base_norm
    )

    raw_norm = float(np.linalg.norm(values["geometry"]["retained_hat"]))
    tangent_norm = float(np.linalg.norm(tangent))
    epsilon = min(
        1.0e-5,
        finite_difference_relative_step * max(raw_norm, 1.0) / max(tangent_norm, 1.0e-30),
    )
    plus = compact_gamma_snapshot(raw + epsilon * tangent, nu, shell)
    minus = compact_gamma_snapshot(raw - epsilon * tangent, nu, shell)
    off_fd_residual = None
    if all(item["positive_part_branch"] == "strict_positive_transfer" for item in (plus, minus)):
        plus_off = float(mechanism_accounting(plus)["signed_contributions"][OFF_MECHANISM])
        minus_off = float(mechanism_accounting(minus)["signed_contributions"][OFF_MECHANISM])
        finite_difference = (plus_off - minus_off) / (2.0 * epsilon)
        off_fd_residual = abs(finite_difference - full_derivative)

    return {
        "resolved": True,
        "gamma": float(snapshot["gamma"]),
        "compact_potential": float(snapshot["compact_gamma_potential_B"]),
        "escape_supply": escape,
        "off_signed_mechanism": float(accounting["signed_contributions"][OFF_MECHANISM]),
        "off_mechanism_active_in_escape": bool(
            float(accounting["signed_contributions"][OFF_MECHANISM]) < 0.0
        ),
        "off_derivative": full_derivative,
        "base_norm_XK": base_norm,
        "packet_energy_tangent_residual": tangent_residual,
        "packet_orientation_second_moment": orientation.tolist(),
        "shell_components": shell_components,
        "angular_energy_rows": angular_rows,
        "shell_derivative_reconstruction_residual": reconstruction,
        "shell_energy_reconstruction_residual": density_reconstruction,
        "off_derivative_finite_difference_residual": off_fd_residual,
        "mechanism_balance_residual": float(accounting["mechanism_balance_residual"]),
    }


def response_rows(
    profiles: list[dict[str, Any]],
    centers: list[dict[str, Any]],
    trajectories: dict[str, list[dict[str, Any]]],
    *,
    nu: float,
    target_energy: float,
    path_parameters: tuple[float, ...],
    times_per_profile: int,
    tangent_kinds: tuple[str, ...],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for profile in profiles:
        center, _distance = nearest_center(profile, centers)
        shell = int(profile["target_shell"])
        for trajectory_row in dangerous_rows(profile, times_per_profile):
            tau = float(trajectory_row["parabolic_time"])
            member_raw = state_at_time(trajectories[profile["profile_id"]], tau)
            center_raw = state_at_time(trajectories[center["profile_id"]], tau)
            for parameter in path_parameters:
                state, path_tangent, normalization_residual = path_state_tangent(
                    center_raw,
                    member_raw,
                    parameter,
                    nu=nu,
                    shell=shell,
                    target_energy=target_energy,
                )
                geometry = _state_geometry(state, nu, shell)
                tangents = {"path": path_tangent, "rhs": geometry["total_rhs_hat"]}
                unknown = set(tangent_kinds) - set(tangents)
                if unknown:
                    raise ValueError(f"unsupported tangent kinds: {sorted(unknown)}")
                for kind in tangent_kinds:
                    rows.append({
                        "profile_id": profile["profile_id"],
                        "center_profile_id": center["profile_id"],
                        "cutoff": int(profile["cutoff"]),
                        "target_shell": shell,
                        "parabolic_time": tau,
                        "path_parameter": float(parameter),
                        "tangent_kind": kind,
                        "normalization_residual": normalization_residual,
                        "response": off_response(
                            state,
                            tangents[kind],
                            nu=nu,
                            shell=shell,
                        ),
                    })
    return rows


def fit_candidate(
    rows: list[dict[str, Any]],
    *,
    shell_exponent: float,
    angular_eta: float,
    tail_radius: int,
    slack: float,
) -> dict[str, Any]:
    resolved = [row for row in rows if row["response"]["resolved"]]
    unresolved = [row for row in rows if not row["response"]["resolved"]]
    metrics = [
        candidate_metrics(
            row["response"],
            shell_exponent=shell_exponent,
            angular_eta=angular_eta,
            tail_radius=tail_radius,
        )
        for row in resolved
    ]
    finite = (
        bool(resolved)
        and not unresolved
        and all(math.isfinite(value) for item in metrics for value in item.values())
    )
    raw = max((item["near_schur_quotient"] for item in metrics), default=math.inf)
    fitted = raw * (1.0 + slack) if finite else math.inf
    return {
        "shell_exponent": shell_exponent,
        "angular_eta": angular_eta,
        "tail_radius": tail_radius,
        "row_count": len(rows),
        "resolved_row_count": len(resolved),
        "unresolved_row_count": len(unresolved),
        "unresolved_reasons": sorted({
            row["response"].get("reason") for row in unresolved
        }),
        "raw_near_schur_constant": raw,
        "fitted_near_schur_constant": fitted,
        "maximum_calibration_tail_quotient": max(
            (item["tail_quotient"] for item in metrics), default=None
        ),
        "maximum_calibration_full_quotient": max(
            (item["full_quotient"] for item in metrics), default=None
        ),
        "slack": slack,
        "finite_candidate": finite,
    }


def evaluate_candidate(
    rows: list[dict[str, Any]], candidate: dict[str, Any]
) -> dict[str, Any]:
    evaluated: list[dict[str, Any]] = []
    constant = float(candidate["fitted_near_schur_constant"])
    for row in rows:
        base = {key: row[key] for key in (
            "profile_id",
            "center_profile_id",
            "cutoff",
            "target_shell",
            "parabolic_time",
            "path_parameter",
            "tangent_kind",
        )}
        response = row["response"]
        if not response["resolved"]:
            evaluated.append({
                **base,
                "resolved": False,
                "survives": False,
                "reason": response.get("reason"),
            })
            continue
        metrics = candidate_metrics(
            response,
            shell_exponent=float(candidate["shell_exponent"]),
            angular_eta=float(candidate["angular_eta"]),
            tail_radius=int(candidate["tail_radius"]),
        )
        near_budget = constant * float(response["escape_supply"]) * metrics["weighted_norm"]
        near_margin = near_budget - metrics["near_absolute_response"]
        full_margin = (
            near_budget
            + metrics["tail_absolute_response"]
            - metrics["full_absolute_response"]
        )
        evaluated.append({
            **base,
            "resolved": True,
            **metrics,
            "near_schur_budget": near_budget,
            "near_schur_margin": near_margin,
            "full_split_margin": full_margin,
            "survives": near_margin >= -1.0e-10 and full_margin >= -1.0e-10,
        })
    resolved = [row for row in evaluated if row["resolved"]]
    return {
        "row_count": len(evaluated),
        "resolved_row_count": len(resolved),
        "unresolved_row_count": len(evaluated) - len(resolved),
        "minimum_near_schur_margin": min(
            (row["near_schur_margin"] for row in resolved), default=None
        ),
        "minimum_full_split_margin": min(
            (row["full_split_margin"] for row in resolved), default=None
        ),
        "maximum_full_quotient": max(
            (row["full_quotient"] for row in resolved), default=None
        ),
        "maximum_tail_quotient": max(
            (row["tail_quotient"] for row in resolved), default=None
        ),
        "maximum_tail_over_full_response": max(
            (row["tail_over_full_response"] for row in resolved), default=None
        ),
        "sampled_offpacket_schur_split_survives": (
            bool(evaluated) and all(row["survives"] for row in evaluated)
        ),
        "rows": evaluated,
    }


def exact_matched_profile(
    source: dict[str, Any], split: str, cutoff: int, **kwargs: Any
) -> dict[str, Any]:
    parameters = PacketParameters(**source["parameters"])
    profile = build_profile(
        split=split,
        seed=int(source["derived_state_seed"]),
        parameters=parameters,
        cutoff=cutoff,
        target_shell=int(source["target_shell"]),
        **kwargs,
    )
    profile["base_parameters"] = asdict(parameters)
    profile["perturbation_sample_index"] = 0
    profile["derived_state_seed"] = int(source["derived_state_seed"])
    return profile


def select_adverse_profiles(
    profiles: list[dict[str, Any]], rows: list[dict[str, Any]], verify_count: int
) -> list[dict[str, Any]]:
    score_by_profile: dict[str, float] = {}
    for row in rows:
        response = row["response"]
        if not response["resolved"]:
            score = math.inf
        else:
            score = abs(float(response["off_derivative"])) / max(
                float(response["escape_supply"]) * float(response["base_norm_XK"]),
                1.0e-30,
            )
        score_by_profile[row["profile_id"]] = max(
            score_by_profile.get(row["profile_id"], -math.inf), score
        )
    selected: list[dict[str, Any]] = []
    for shell in sorted({int(profile["target_shell"]) for profile in profiles}):
        local = [profile for profile in profiles if int(profile["target_shell"]) == shell]
        local.sort(key=lambda profile: -score_by_profile.get(profile["profile_id"], -math.inf))
        selected.extend(local[:verify_count])
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
    phase_jitter: float,
    log_ratio_jitter: float,
    log_satellite_jitter: float,
    gamma_threshold: float,
    path_parameters: tuple[float, ...],
    tangent_kinds: tuple[str, ...],
    times_per_profile: int,
    shell_exponents: tuple[float, ...],
    angular_etas: tuple[float, ...],
    tail_radii: tuple[int, ...],
    schur_slack: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
    verify_count: int,
) -> dict[str, Any]:
    if any(value < 0.0 for value in shell_exponents + angular_etas):
        raise ValueError("weight parameters must be nonnegative")
    if any(radius < 0 for radius in tail_radii):
        raise ValueError("tail radii must be nonnegative")
    centers, calibration, holdout = build_profile_sets(
        base_parameters=base_parameters,
        center_seeds=center_seeds,
        calibration_seeds=calibration_seeds,
        holdout_seeds=holdout_seeds,
        samples_per_base=samples_per_base,
        calibration_jitter_scale=1.0,
        holdout_jitter_scale=1.0,
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
    common = dict(
        nu=nu,
        input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    trajectories = {
        profile["profile_id"]: reconstruct_trajectory(profile, **common)
        for profile in centers + calibration + holdout
    }
    calibration_rows = response_rows(
        calibration,
        centers,
        trajectories,
        nu=nu,
        target_energy=target_packet_energy,
        path_parameters=path_parameters,
        times_per_profile=times_per_profile,
        tangent_kinds=tangent_kinds,
    )
    holdout_rows = response_rows(
        holdout,
        centers,
        trajectories,
        nu=nu,
        target_energy=target_packet_energy,
        path_parameters=path_parameters,
        times_per_profile=times_per_profile,
        tangent_kinds=tangent_kinds,
    )

    candidates: list[dict[str, Any]] = []
    for shell_exponent in shell_exponents:
        for angular_eta in angular_etas:
            for tail_radius in tail_radii:
                fitted = fit_candidate(
                    calibration_rows,
                    shell_exponent=shell_exponent,
                    angular_eta=angular_eta,
                    tail_radius=tail_radius,
                    slack=schur_slack,
                )
                fitted["holdout_evaluation"] = evaluate_candidate(holdout_rows, fitted)
                candidates.append(fitted)

    selected_profiles = select_adverse_profiles(holdout, holdout_rows, verify_count)
    matched_rows: list[dict[str, Any]] = []
    matched_profile_count = 0
    build_kwargs = dict(
        nu=nu,
        input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    for member_source in selected_profiles:
        center_source, _distance = nearest_center(member_source, centers)
        for cutoff in verify_cutoffs:
            member = exact_matched_profile(
                member_source, "matched-member", cutoff, **build_kwargs
            )
            center = exact_matched_profile(
                center_source, "matched-center", cutoff, **build_kwargs
            )
            matched_profile_count += 1
            local = {
                profile["profile_id"]: reconstruct_trajectory(profile, **common)
                for profile in (member, center)
            }
            matched_rows.extend(response_rows(
                [member],
                [center],
                local,
                nu=nu,
                target_energy=target_packet_energy,
                path_parameters=path_parameters,
                times_per_profile=times_per_profile,
                tangent_kinds=tangent_kinds,
            ))

    for candidate in candidates:
        candidate["matched_evaluation"] = evaluate_candidate(matched_rows, candidate)
        candidate["full_chain_survives"] = bool(candidate["finite_candidate"])
        candidate["full_chain_survives"] = candidate["full_chain_survives"] and bool(
            candidate["holdout_evaluation"]["sampled_offpacket_schur_split_survives"]
        ) and bool(
            candidate["matched_evaluation"]["sampled_offpacket_schur_split_survives"]
        )

    survivors = [candidate for candidate in candidates if candidate["full_chain_survives"]]
    survivors.sort(key=lambda candidate: (
        float(candidate["holdout_evaluation"]["maximum_tail_quotient"]),
        float(candidate["matched_evaluation"]["maximum_tail_quotient"]),
        float(candidate["fitted_near_schur_constant"]),
        float(candidate["shell_exponent"]),
        float(candidate["angular_eta"]),
        int(candidate["tail_radius"]),
    ))
    selected_candidate = survivors[0] if survivors else None

    matched_groups: list[dict[str, Any]] = []
    if selected_candidate is not None:
        group_map: dict[tuple[int, float, float, str], list[dict[str, Any]]] = {}
        for row in selected_candidate["matched_evaluation"]["rows"]:
            if not row["resolved"]:
                continue
            key = (
                int(row["target_shell"]),
                float(row["parabolic_time"]),
                float(row["path_parameter"]),
                str(row["tangent_kind"]),
            )
            group_map.setdefault(key, []).append(row)
        for key, rows in sorted(group_map.items()):
            cutoffs = sorted({int(row["cutoff"]) for row in rows})
            full = [float(row["full_quotient"]) for row in rows]
            tail = [float(row["tail_quotient"]) for row in rows]
            norms = [float(row["weighted_norm"]) for row in rows]
            matched_groups.append({
                "target_shell": key[0],
                "parabolic_time": key[1],
                "path_parameter": key[2],
                "tangent_kind": key[3],
                "observed_cutoffs": cutoffs,
                "matched_cutoff_complete": set(cutoffs) == set(verify_cutoffs),
                "full_quotient_spread": max(full) - min(full),
                "tail_quotient_spread": max(tail) - min(tail),
                "weighted_norm_spread": max(norms) - min(norms),
                "all_rows_survive": all(row["survives"] for row in rows),
            })

    all_rows = calibration_rows + holdout_rows + matched_rows
    resolved_responses = [
        row["response"] for row in all_rows if row["response"]["resolved"]
    ]
    finite = lambda key: [
        float(response[key])
        for response in resolved_responses
        if response.get(key) is not None
    ]
    baseline = next((
        candidate for candidate in candidates
        if float(candidate["shell_exponent"]) == 0.0
        and float(candidate["angular_eta"]) == 0.0
        and int(candidate["tail_radius"]) == max(tail_radii)
    ), None)
    full_survival = (
        selected_candidate is not None
        and bool(matched_groups)
        and all(group["matched_cutoff_complete"] for group in matched_groups)
    )

    return {
        "schema_version": "1.0.0",
        "authority": {
            "exact_finite_galerkin_offpacket_derivative": True,
            "exact_reality_closed_shell_split": True,
            "sampled_weighted_schur_tail_candidate_survives": full_survival,
            "analytic_offpacket_schur_bound_proved": False,
            "analytic_tail_absorption_proved": False,
            "cutoff_shell_uniform_authority": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "off_packet_response": "exact D m_off(u)[h] on the strict positive-transfer branch",
            "shell_partition": "reality-closed dyadic tangent shells relative to target K",
            "angular_defect": "1-khat^T M_K khat for the target-packet Fourier second moment M_K",
            "weighted_norm": "X_K with radial 2^(sigma |j-K|) and projective angular 1+eta*a_K weights",
            "tail": "sum of absolute shell-response contributions with |j-K| greater than the declared radius",
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
            "path_parameters": list(path_parameters),
            "tangent_kinds": list(tangent_kinds),
            "times_per_profile": times_per_profile,
            "shell_exponents": list(shell_exponents),
            "angular_etas": list(angular_etas),
            "tail_radii": list(tail_radii),
            "schur_slack": schur_slack,
            "verify_count_per_shell": verify_count,
        },
        "center_profile_count": len(centers),
        "calibration_profile_count": len(calibration),
        "holdout_profile_count": len(holdout),
        "calibration_row_count": len(calibration_rows),
        "holdout_row_count": len(holdout_rows),
        "matched_profile_count": matched_profile_count,
        "matched_row_count": len(matched_rows),
        "baseline_candidate": baseline,
        "selected_candidate": selected_candidate,
        "candidate_count": len(candidates),
        "surviving_candidate_count": len(survivors),
        "candidates": candidates,
        "matched_cutoff_groups": matched_groups,
        "maximum_shell_derivative_reconstruction_residual": max(
            finite("shell_derivative_reconstruction_residual"), default=None
        ),
        "maximum_shell_energy_reconstruction_residual": max(
            finite("shell_energy_reconstruction_residual"), default=None
        ),
        "maximum_off_derivative_finite_difference_residual": max(
            finite("off_derivative_finite_difference_residual"), default=None
        ),
        "maximum_mechanism_balance_residual": max(
            finite("mechanism_balance_residual"), default=None
        ),
        "maximum_packet_energy_tangent_residual": max(
            finite("packet_energy_tangent_residual"), default=None
        ),
        "calibration_rows": calibration_rows,
        "holdout_rows": holdout_rows,
        "matched_rows": matched_rows,
        "limitations": [
            "the shell split tests only the selected path and Navier-Stokes RHS tangents",
            "the angular weight is a declared projective second-moment candidate, not a derived optimal metric",
            "the fitted near constant is empirical and not the exact pair-incidence Schur certificate",
            "the far-shell tail is measured rather than analytically absorbed",
            "matched N32/N48/N64 cutoffs do not establish continuum compactness",
            "no BKM, global-regularity, or Clay promotion",
        ],
    }


def parse_tangent_kinds(raw: str) -> tuple[str, ...]:
    values = tuple(dict.fromkeys(piece.strip() for piece in raw.split(",") if piece.strip()))
    if not values:
        raise ValueError("expected at least one tangent kind")
    return values


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
    parser.add_argument("--samples-per-base", type=int, default=1)
    parser.add_argument("--phase-jitter", type=float, default=0.8)
    parser.add_argument("--log-ratio-jitter", type=float, default=0.5)
    parser.add_argument("--log-satellite-jitter", type=float, default=0.35)
    parser.add_argument("--gamma-threshold", type=float, default=0.5)
    parser.add_argument("--path-parameters", default="0.5")
    parser.add_argument("--tangent-kinds", default="path,rhs")
    parser.add_argument("--times-per-profile", type=int, default=1)
    parser.add_argument("--shell-exponents", default="0,0.25,0.5,1")
    parser.add_argument("--angular-etas", default="0,0.5,1,2")
    parser.add_argument("--tail-radii", default="1,2")
    parser.add_argument("--schur-slack", type=float, default=0.25)
    parser.add_argument("--end-parabolic-time", type=float, default=0.004)
    parser.add_argument("--output-count", type=int, default=3)
    parser.add_argument("--cfl", type=float, default=0.2)
    parser.add_argument("--verify-count", type=int, default=1)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    result = audit_family(
        search_cutoff=args.search_cutoff,
        verify_cutoffs=parse_int_tuple(args.verify_cutoffs),
        target_shells=parse_int_tuple(args.target_shells),
        nu=args.viscosity,
        input_amplitude=args.input_amplitude,
        target_packet_energy=args.target_packet_energy,
        base_parameters=packet_parameter_grid(
            parse_int_tuple(args.triad_counts),
            parse_float_tuple(args.phase_spreads),
            parse_float_tuple(args.target_ratios),
            parse_float_tuple(args.satellite_fractions),
        ),
        center_seeds=parse_int_tuple(args.center_seeds),
        calibration_seeds=parse_int_tuple(args.calibration_seeds),
        holdout_seeds=parse_int_tuple(args.holdout_seeds),
        samples_per_base=args.samples_per_base,
        phase_jitter=args.phase_jitter,
        log_ratio_jitter=args.log_ratio_jitter,
        log_satellite_jitter=args.log_satellite_jitter,
        gamma_threshold=args.gamma_threshold,
        path_parameters=parse_float_tuple(args.path_parameters),
        tangent_kinds=parse_tangent_kinds(args.tangent_kinds),
        times_per_profile=args.times_per_profile,
        shell_exponents=parse_float_tuple(args.shell_exponents),
        angular_etas=parse_float_tuple(args.angular_etas),
        tail_radii=parse_int_tuple(args.tail_radii),
        schur_slack=args.schur_slack,
        end_parabolic_time=args.end_parabolic_time,
        output_count=args.output_count,
        cfl=args.cfl,
        verify_count=args.verify_count,
    )
    atomic_json(args.output_json, result, args.pretty)
    selected = result["selected_candidate"]
    print(json.dumps({
        "output_json": str(args.output_json),
        "surviving_candidate_count": result["surviving_candidate_count"],
        "selected_shell_exponent": None if selected is None else selected["shell_exponent"],
        "selected_angular_eta": None if selected is None else selected["angular_eta"],
        "selected_tail_radius": None if selected is None else selected["tail_radius"],
        "selected_near_constant": None if selected is None else selected["fitted_near_schur_constant"],
        "sampled_chain_survives": result["authority"][
            "sampled_weighted_schur_tail_candidate_survives"
        ],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
