#!/usr/bin/env python3
"""Fit and falsify a common compact-Gamma residence upper bound on a finite packet net.

The preceding multi-triad audit supplied pointwise finite-Galerkin evidence for

    Gamma_K >= lambda  ->  E_K >= c_lambda,
    R_K <= theta E_K,  theta < 1,

where E_K and R_K are the one-sided compact-Gamma mechanism totals.  This lane
adds the integrated remainder needed by the existing Agda absorption theorem,

    C_theta(I) = integral_I max(R_K - theta E_K, 0) d tau,

and searches for a common upper bound on

    B_K(t0) + C_theta(I),

across a declared normalized packet class.  Since 0 <= B_K <= 1 exactly, the
analytic target reduces to a cutoff/shell/profile-uniform bound on C_theta.

The finite-net section uses center, calibration, and held-out seeds.  It fits an
empirical local oscillation rate for C_theta in normalized Fourier-state
L2 distance, then checks the resulting center-plus-allowance bound on held-out
profiles and matched cutoffs.  This is a falsification instrument, not a proof
of compactness or a Lipschitz theorem.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import numpy as np

from ns_compact_gamma_multitriad_evolved_audit import (
    angular_packet_metrics,
    evolved_states,
    multitriad_diffuse_hat,
    state_row,
)


@dataclass(frozen=True)
class PacketParameters:
    triad_count: int
    phase_spread: float
    target_ratio: float
    satellite_fraction: float

    @property
    def key(self) -> str:
        return (
            f"triads-{self.triad_count}-spread-{self.phase_spread:.8g}-"
            f"ratio-{self.target_ratio:.8g}-sat-{self.satellite_fraction:.8g}"
        )


def atomic_json(path: Path, payload: dict[str, Any], pretty: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        temporary = Path(handle.name)
        json.dump(payload, handle, indent=2 if pretty else None, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def parse_int_tuple(raw: str) -> tuple[int, ...]:
    values = tuple(sorted({int(piece.strip()) for piece in raw.split(",") if piece.strip()}))
    if not values:
        raise ValueError("expected at least one integer")
    return values


def parse_float_tuple(raw: str) -> tuple[float, ...]:
    values = tuple(float(piece.strip()) for piece in raw.split(",") if piece.strip())
    if not values or any(not math.isfinite(value) for value in values):
        raise ValueError("expected finite comma-separated floats")
    return values


def packet_parameter_grid(
    triad_counts: tuple[int, ...],
    phase_spreads: tuple[float, ...],
    target_ratios: tuple[float, ...],
    satellite_fractions: tuple[float, ...],
) -> tuple[PacketParameters, ...]:
    parameters = tuple(
        PacketParameters(triad_count, phase_spread, target_ratio, satellite_fraction)
        for triad_count in triad_counts
        for phase_spread in phase_spreads
        for target_ratio in target_ratios
        for satellite_fraction in satellite_fractions
    )
    if any(parameter.triad_count < 1 for parameter in parameters):
        raise ValueError("triad counts must be positive")
    if any(parameter.phase_spread < 0.0 for parameter in parameters):
        raise ValueError("phase spreads must be nonnegative")
    if any(parameter.target_ratio <= 0.0 for parameter in parameters):
        raise ValueError("target ratios must be positive")
    if any(not 0.0 < parameter.satellite_fraction <= 1.0 for parameter in parameters):
        raise ValueError("satellite fractions must lie in (0,1]")
    return parameters


def normalize_packet_energy(
    raw_hat: np.ndarray,
    target_shell: int,
    target_packet_energy: float,
) -> tuple[np.ndarray, dict[str, float]]:
    if not math.isfinite(target_packet_energy) or target_packet_energy <= 0.0:
        raise ValueError("target packet energy must be finite and positive")
    before = angular_packet_metrics(raw_hat, target_shell)
    packet_energy = float(before["packet_energy"])
    if packet_energy <= 1.0e-30:
        raise ValueError("cannot normalize a zero-energy target packet")
    factor = math.sqrt(target_packet_energy / packet_energy)
    normalized = np.asarray(raw_hat, dtype=np.complex128) * factor
    after = angular_packet_metrics(normalized, target_shell)
    residual = abs(float(after["packet_energy"]) - target_packet_energy)
    return normalized, {
        "target_packet_energy": target_packet_energy,
        "pre_normalization_packet_energy": packet_energy,
        "scale_factor": factor,
        "post_normalization_packet_energy": float(after["packet_energy"]),
        "normalization_residual": residual,
    }


def state_feature(raw_hat: np.ndarray) -> np.ndarray:
    """Physical Fourier coefficient vector used by the empirical finite net."""
    n = int(raw_hat.shape[0])
    field = np.asarray(raw_hat, dtype=np.complex128) / float(n ** 3)
    feature = np.concatenate((field.real.ravel(), field.imag.ravel()))
    if not np.all(np.isfinite(feature)):
        raise ValueError("non-finite state feature")
    return feature


def mechanism_rates(row: dict[str, Any]) -> tuple[float, float]:
    accounting = row.get("mechanism_accounting")
    if accounting is None:
        raise ValueError("compact-Gamma branch unresolved in trajectory")
    escape = float(accounting["escape_supply"])
    replenishment = float(accounting["replenishment"])
    if not (math.isfinite(escape) and math.isfinite(replenishment)):
        raise ValueError("non-finite mechanism rate")
    if escape < -1.0e-12 or replenishment < -1.0e-12:
        raise ValueError("one-sided mechanism rates must be nonnegative")
    return max(escape, 0.0), max(replenishment, 0.0)


def integrate_profile_remainder(
    rows: Iterable[dict[str, Any]], theta: float
) -> dict[str, Any]:
    if not math.isfinite(theta) or theta < 0.0:
        raise ValueError("theta must be finite and nonnegative")
    ordered = sorted(rows, key=lambda row: float(row["parabolic_time"]))
    if not ordered:
        raise ValueError("profile trajectory is empty")
    times = [float(row["parabolic_time"]) for row in ordered]
    if len(times) != len(set(times)) or any(
        right <= left for left, right in zip(times, times[1:])
    ):
        raise ValueError("profile trajectory times must be strictly increasing")

    defects: list[float] = []
    ratios: list[float | None] = []
    dangerous_escape: list[float] = []
    for row in ordered:
        escape, replenishment = mechanism_rates(row)
        defects.append(max(replenishment - theta * escape, 0.0))
        ratios.append(replenishment / escape if escape > 0.0 else None)
        if bool(row.get("dangerous", False)):
            dangerous_escape.append(escape)

    remainder = 0.0
    for index in range(len(ordered) - 1):
        duration = times[index + 1] - times[index]
        remainder += 0.5 * duration * (defects[index] + defects[index + 1])

    initial_potential = float(ordered[0]["compact_potential"])
    if not -1.0e-12 <= initial_potential <= 1.0 + 1.0e-12:
        raise ValueError("compact-Gamma potential left [0,1]")
    initial_potential = min(max(initial_potential, 0.0), 1.0)
    return {
        "row_count": len(ordered),
        "initial_compact_potential": initial_potential,
        "remainder_C_theta": remainder,
        "member_upper_B0_plus_C": initial_potential + remainder,
        "unit_reduced_upper_1_plus_C": 1.0 + remainder,
        "maximum_pointwise_defect": max(defects),
        "pointwise_defects": defects,
        "replenishment_over_escape": ratios,
        "dangerous_row_count": sum(bool(row.get("dangerous", False)) for row in ordered),
        "minimum_dangerous_escape": min(dangerous_escape) if dangerous_escape else None,
        "all_rows_resolved": True,
    }


def nearest_center(
    profile: dict[str, Any], centers: list[dict[str, Any]]
) -> tuple[dict[str, Any], float]:
    compatible = [
        center
        for center in centers
        if int(center["target_shell"]) == int(profile["target_shell"])
        and int(center["parameters"]["triad_count"])
        == int(profile["parameters"]["triad_count"])
    ]
    if not compatible:
        raise ValueError("no compatible finite-net center")
    feature = profile["feature"]
    distances = [float(np.linalg.norm(feature - center["feature"])) for center in compatible]
    index = int(np.argmin(distances))
    return compatible[index], distances[index]


def fit_local_oscillation(
    centers: list[dict[str, Any]],
    calibration: list[dict[str, Any]],
    holdout: list[dict[str, Any]],
    *,
    slope_slack: float,
) -> dict[str, Any]:
    if not centers or not calibration or not holdout:
        raise ValueError("center, calibration, and holdout profile sets must be nonempty")
    if not math.isfinite(slope_slack) or slope_slack < 0.0:
        raise ValueError("slope slack must be finite and nonnegative")

    calibration_rows: list[dict[str, Any]] = []
    observed_slopes: list[float] = []
    singular_excess = False
    for profile in calibration:
        center, distance = nearest_center(profile, centers)
        excess = max(
            float(profile["envelope"]["remainder_C_theta"])
            - float(center["envelope"]["remainder_C_theta"]),
            0.0,
        )
        if distance <= 1.0e-14:
            slope = 0.0 if excess <= 1.0e-12 else math.inf
            singular_excess = singular_excess or not math.isfinite(slope)
        else:
            slope = excess / distance
        if math.isfinite(slope):
            observed_slopes.append(slope)
        calibration_rows.append(
            {
                "profile_id": profile["profile_id"],
                "center_profile_id": center["profile_id"],
                "distance": distance,
                "positive_remainder_excess": excess,
                "observed_one_sided_slope": slope,
            }
        )

    if singular_excess:
        fitted_slope = math.inf
    else:
        base_slope = max(observed_slopes, default=0.0)
        fitted_slope = base_slope * (1.0 + slope_slack)

    holdout_rows: list[dict[str, Any]] = []
    violations: list[dict[str, Any]] = []
    coverage_radius = 0.0
    for profile in holdout:
        center, distance = nearest_center(profile, centers)
        coverage_radius = max(coverage_radius, distance)
        center_remainder = float(center["envelope"]["remainder_C_theta"])
        predicted = (
            math.inf if not math.isfinite(fitted_slope)
            else center_remainder + fitted_slope * distance
        )
        actual = float(profile["envelope"]["remainder_C_theta"])
        margin = predicted - actual
        row = {
            "profile_id": profile["profile_id"],
            "center_profile_id": center["profile_id"],
            "distance": distance,
            "actual_remainder_C_theta": actual,
            "predicted_remainder_upper": predicted,
            "prediction_margin": margin,
            "bound_holds": margin >= -1.0e-10,
        }
        holdout_rows.append(row)
        if not row["bound_holds"]:
            violations.append(row)

    center_upper = max(float(center["envelope"]["remainder_C_theta"]) for center in centers)
    allowance = (
        math.inf if not math.isfinite(fitted_slope)
        else fitted_slope * coverage_radius
    )
    common_remainder_upper = center_upper + allowance
    common_member_upper = 1.0 + common_remainder_upper
    return {
        "center_count": len(centers),
        "calibration_count": len(calibration),
        "holdout_count": len(holdout),
        "calibration_rows": calibration_rows,
        "holdout_rows": holdout_rows,
        "fitted_one_sided_remainder_slope": fitted_slope,
        "coverage_radius": coverage_radius,
        "oscillation_allowance": allowance,
        "center_remainder_upper": center_upper,
        "common_remainder_upper": common_remainder_upper,
        "common_member_upper_1_plus_remainder": common_member_upper,
        "holdout_violation_count": len(violations),
        "holdout_violations": violations,
        "sampled_finite_net_bound_survives_holdout": not violations
        and math.isfinite(common_member_upper),
    }


def build_profile(
    *,
    split: str,
    seed: int,
    parameters: PacketParameters,
    cutoff: int,
    target_shell: int,
    nu: float,
    input_amplitude: float,
    target_packet_energy: float,
    gamma_threshold: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
) -> dict[str, Any]:
    raw, constructor = multitriad_diffuse_hat(
        cutoff,
        target_shell,
        triad_count=parameters.triad_count,
        input_amplitude=input_amplitude,
        target_ratio=parameters.target_ratio,
        satellite_fraction=parameters.satellite_fraction,
        phase_spread=parameters.phase_spread,
        seed=seed,
    )
    raw, normalization = normalize_packet_energy(
        raw, target_shell, target_packet_energy
    )
    constructor = dict(constructor)
    constructor["normalization"] = normalization
    trajectory = evolved_states(
        raw,
        nu,
        target_shell,
        end_parabolic_time=end_parabolic_time,
        output_count=output_count,
        cfl=cfl,
    )
    profile_id = (
        f"{split}-seed-{seed}-{parameters.key}-shell-{target_shell}-N{cutoff}"
    )
    rows: list[dict[str, Any]] = []
    for state in trajectory:
        row = state_row(
            state["raw_hat"],
            cutoff=cutoff,
            target_shell=target_shell,
            nu=nu,
            gamma_threshold=gamma_threshold,
            candidate_id=profile_id,
            parabolic_time=float(state["parabolic_time"]),
            physical_time=float(state["physical_time"]),
            constructor=constructor,
        )
        row["steps_since_previous_output"] = int(state["steps_since_previous_output"])
        rows.append(row)
    return {
        "profile_id": profile_id,
        "split": split,
        "seed": seed,
        "cutoff": cutoff,
        "target_shell": target_shell,
        "parameters": {
            "triad_count": parameters.triad_count,
            "phase_spread": parameters.phase_spread,
            "target_ratio": parameters.target_ratio,
            "satellite_fraction": parameters.satellite_fraction,
        },
        "feature": state_feature(raw),
        "normalization": normalization,
        "rows": rows,
    }


def fit_theta_and_c_lambda(
    training_profiles: list[dict[str, Any]],
    *,
    gamma_threshold: float,
    theta_slack: float,
    c_lambda_slack: float,
) -> dict[str, Any]:
    dangerous: list[tuple[float, float]] = []
    for profile in training_profiles:
        for row in profile["rows"]:
            if not bool(row["dangerous"]):
                continue
            escape, replenishment = mechanism_rates(row)
            if escape <= 0.0:
                dangerous.append((math.inf, escape))
            else:
                dangerous.append((replenishment / escape, escape))
    if not dangerous:
        raise ValueError("training family contains no dangerous rows")
    ratios = [ratio for ratio, _escape in dangerous]
    escapes = [escape for _ratio, escape in dangerous]
    theta_raw = max(ratios)
    theta_fit = theta_raw + theta_slack
    c_raw = min(escapes)
    c_fit = (1.0 - c_lambda_slack) * c_raw
    return {
        "training_dangerous_row_count": len(dangerous),
        "training_theta_envelope": theta_raw,
        "fitted_theta": theta_fit,
        "training_c_lambda_envelope": c_raw,
        "fitted_c_lambda": c_fit,
        "strict_theta": math.isfinite(theta_fit) and theta_fit < 1.0,
        "positive_c_lambda": math.isfinite(c_fit) and c_fit > 0.0,
    }


def check_danger_constants(
    profiles: list[dict[str, Any]],
    theta: float,
    c_lambda: float,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for profile in profiles:
        for row in profile["rows"]:
            if not bool(row["dangerous"]):
                continue
            escape, replenishment = mechanism_rates(row)
            ratio = replenishment / escape if escape > 0.0 else math.inf
            rows.append(
                {
                    "profile_id": profile["profile_id"],
                    "parabolic_time": float(row["parabolic_time"]),
                    "gamma": float(row["gamma"]),
                    "escape_supply": escape,
                    "replenishment_over_escape": ratio,
                    "theta_margin": theta - ratio,
                    "c_lambda_margin": escape - c_lambda,
                    "absorbed": ratio <= theta + 1.0e-10,
                    "danger_expenditure": escape >= c_lambda - 1.0e-10,
                }
            )
    return {
        "dangerous_row_count": len(rows),
        "rows": rows,
        "all_dangerous_rows_absorbed": bool(rows)
        and all(row["absorbed"] for row in rows),
        "all_dangerous_rows_spend_c_lambda": bool(rows)
        and all(row["danger_expenditure"] for row in rows),
        "minimum_theta_margin": min((row["theta_margin"] for row in rows), default=None),
        "minimum_c_lambda_margin": min(
            (row["c_lambda_margin"] for row in rows), default=None
        ),
    }


def strip_profile(profile: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in profile.items() if key != "feature"}


def audit_family(
    *,
    search_cutoff: int,
    verify_cutoffs: tuple[int, ...],
    target_shells: tuple[int, ...],
    nu: float,
    input_amplitude: float,
    target_packet_energy: float,
    parameters: tuple[PacketParameters, ...],
    center_seeds: tuple[int, ...],
    calibration_seeds: tuple[int, ...],
    holdout_seeds: tuple[int, ...],
    gamma_threshold: float,
    theta_slack: float,
    c_lambda_slack: float,
    slope_slack: float,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
    verify_count: int,
) -> dict[str, Any]:
    split_seeds = {
        "center": center_seeds,
        "calibration": calibration_seeds,
        "holdout": holdout_seeds,
    }
    all_seeds = [seed for seeds in split_seeds.values() for seed in seeds]
    if len(all_seeds) != len(set(all_seeds)):
        raise ValueError("center, calibration, and holdout seeds must be disjoint")
    if any(seed < 0 for seed in all_seeds):
        raise ValueError("seeds must be nonnegative")
    if output_count < 2:
        raise ValueError("output count must be at least two for remainder integration")
    if end_parabolic_time <= 0.0:
        raise ValueError("end parabolic time must be positive")
    if verify_count < 1:
        raise ValueError("verify count must be positive")

    profiles: list[dict[str, Any]] = []
    for split, seeds in split_seeds.items():
        for seed in seeds:
            for parameter in parameters:
                for shell in target_shells:
                    profiles.append(
                        build_profile(
                            split=split,
                            seed=seed,
                            parameters=parameter,
                            cutoff=search_cutoff,
                            target_shell=shell,
                            nu=nu,
                            input_amplitude=input_amplitude,
                            target_packet_energy=target_packet_energy,
                            gamma_threshold=gamma_threshold,
                            end_parabolic_time=end_parabolic_time,
                            output_count=output_count,
                            cfl=cfl,
                        )
                    )

    centers = [profile for profile in profiles if profile["split"] == "center"]
    calibration = [
        profile for profile in profiles if profile["split"] == "calibration"
    ]
    holdout = [profile for profile in profiles if profile["split"] == "holdout"]
    training = centers + calibration
    fitted = fit_theta_and_c_lambda(
        training,
        gamma_threshold=gamma_threshold,
        theta_slack=theta_slack,
        c_lambda_slack=c_lambda_slack,
    )
    theta = float(fitted["fitted_theta"])
    c_lambda = float(fitted["fitted_c_lambda"])

    for profile in profiles:
        profile["envelope"] = integrate_profile_remainder(profile["rows"], theta)

    finite_net = fit_local_oscillation(
        centers,
        calibration,
        holdout,
        slope_slack=slope_slack,
    )
    split_constant_checks = {
        split: check_danger_constants(
            [profile for profile in profiles if profile["split"] == split],
            theta,
            c_lambda,
        )
        for split in split_seeds
    }

    ranked_holdout = sorted(
        holdout,
        key=lambda profile: (
            -float(profile["envelope"]["remainder_C_theta"]),
            -max(float(row["gamma"]) for row in profile["rows"]),
        ),
    )
    selected_base = ranked_holdout[:verify_count]
    selected_parameter_keys = {
        (
            profile["seed"],
            PacketParameters(**profile["parameters"]),
        )
        for profile in selected_base
    }
    matched_profiles: list[dict[str, Any]] = []
    for seed, parameter in selected_parameter_keys:
        for cutoff in verify_cutoffs:
            for shell in target_shells:
                profile = build_profile(
                    split="matched-holdout",
                    seed=int(seed),
                    parameters=parameter,
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
                profile["envelope"] = integrate_profile_remainder(profile["rows"], theta)
                matched_profiles.append(profile)

    matched_checks = check_danger_constants(matched_profiles, theta, c_lambda)
    common_upper = float(finite_net["common_member_upper_1_plus_remainder"])
    matched_upper_violations = [
        profile
        for profile in matched_profiles
        if float(profile["envelope"]["member_upper_B0_plus_C"])
        > common_upper + 1.0e-10
    ]

    matched_group_map: dict[tuple[int, str], list[dict[str, Any]]] = {}
    for profile in matched_profiles:
        key = (int(profile["target_shell"]), str(profile["parameters"]))
        matched_group_map.setdefault(key, []).append(profile)
    matched_groups: list[dict[str, Any]] = []
    for (shell, parameter_key), group in matched_group_map.items():
        group.sort(key=lambda profile: int(profile["cutoff"]))
        values = [
            float(profile["envelope"]["member_upper_B0_plus_C"])
            for profile in group
        ]
        remainders = [
            float(profile["envelope"]["remainder_C_theta"]) for profile in group
        ]
        matched_groups.append(
            {
                "target_shell": shell,
                "parameters": parameter_key,
                "observed_cutoffs": [int(profile["cutoff"]) for profile in group],
                "matched_cutoff_complete": set(int(profile["cutoff"]) for profile in group)
                == set(verify_cutoffs),
                "member_upper_spread": max(values) - min(values),
                "remainder_spread": max(remainders) - min(remainders),
                "maximum_member_upper": max(values),
                "below_common_upper": max(values) <= common_upper + 1.0e-10,
            }
        )

    all_rows = [row for profile in profiles + matched_profiles for row in profile["rows"]]
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
    normalization_residuals = [
        float(profile["normalization"]["normalization_residual"])
        for profile in profiles + matched_profiles
    ]

    full_chain_survives = (
        bool(fitted["strict_theta"])
        and bool(fitted["positive_c_lambda"])
        and all(
            checks["all_dangerous_rows_absorbed"]
            and checks["all_dangerous_rows_spend_c_lambda"]
            for checks in split_constant_checks.values()
        )
        and bool(finite_net["sampled_finite_net_bound_survives_holdout"])
        and matched_checks["all_dangerous_rows_absorbed"]
        and matched_checks["all_dangerous_rows_spend_c_lambda"]
        and not matched_upper_violations
        and bool(matched_groups)
        and all(group["matched_cutoff_complete"] for group in matched_groups)
    )
    margin_rate = (1.0 - theta) * c_lambda
    residence_coefficient = common_upper / margin_rate if margin_rate > 0.0 else math.inf

    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_common_u_audit": True,
            "normalized_packet_class_audit": True,
            "center_calibration_holdout_net": True,
            "sampled_full_chain_survives": full_chain_survives,
            "analytic_local_oscillation_bound_proved": False,
            "cutoff_shell_uniform_authority": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "C_theta": "trapezoidal integral in parabolic time of max(R_K-theta E_K,0)",
            "member_upper": "B_K(t0)+C_theta",
            "unit_reduced_upper": "1+C_theta using the exact compact-potential bound B_K<=1",
            "finite_net_distance": "physical Fourier coefficient L2 distance at the search cutoff",
            "oscillation_allowance": "fitted one-sided remainder slope times held-out coverage radius",
        },
        "parameters": {
            "search_cutoff": search_cutoff,
            "verify_cutoffs": list(verify_cutoffs),
            "target_shells": list(target_shells),
            "viscosity": nu,
            "input_amplitude_before_normalization": input_amplitude,
            "target_packet_energy": target_packet_energy,
            "packet_parameter_count": len(parameters),
            "packet_parameters": [parameter.__dict__ for parameter in parameters],
            "center_seeds": list(center_seeds),
            "calibration_seeds": list(calibration_seeds),
            "holdout_seeds": list(holdout_seeds),
            "gamma_threshold": gamma_threshold,
            "theta_slack": theta_slack,
            "c_lambda_slack": c_lambda_slack,
            "slope_slack": slope_slack,
            "end_parabolic_time": end_parabolic_time,
            "output_count": output_count,
            "cfl": cfl,
            "verify_count": verify_count,
        },
        "profile_count": len(profiles),
        "center_profile_count": len(centers),
        "calibration_profile_count": len(calibration),
        "holdout_profile_count": len(holdout),
        "matched_profile_count": len(matched_profiles),
        "fitted_danger_constants": fitted,
        "split_danger_constant_checks": split_constant_checks,
        "finite_net_remainder_envelope": finite_net,
        "sampled_common_member_upper": common_upper,
        "sampled_margin_consumption_rate": margin_rate,
        "sampled_residence_coefficient": residence_coefficient,
        "matched_danger_constant_checks": matched_checks,
        "matched_upper_violation_count": len(matched_upper_violations),
        "matched_cutoff_groups": matched_groups,
        "maximum_matched_member_upper_spread": max(
            (group["member_upper_spread"] for group in matched_groups), default=None
        ),
        "maximum_matched_remainder_spread": max(
            (group["remainder_spread"] for group in matched_groups), default=None
        ),
        "maximum_relative_divergence_residual": max(divergence_residuals, default=None),
        "maximum_mechanism_balance_residual": max(mechanism_residuals, default=None),
        "maximum_finite_difference_residual": max(fd_residuals, default=None),
        "maximum_normalization_residual": max(normalization_residuals, default=None),
        "profiles": [strip_profile(profile) for profile in profiles],
        "matched_profiles": [strip_profile(profile) for profile in matched_profiles],
        "limitations": [
            "the finite-net slope is fitted from samples rather than proved analytically",
            "the packet class is a declared finite-dimensional family, not all critical profiles",
            "short matched-cutoff evolution does not establish compactness",
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
    parser.add_argument("--triad-counts", default="2,4")
    parser.add_argument("--phase-spreads", default="0.0,0.35,0.7")
    parser.add_argument("--target-ratios", default="2.0,2.5,3.0")
    parser.add_argument("--satellite-fractions", default="0.4,0.7,1.0")
    parser.add_argument("--center-seeds", default="1")
    parser.add_argument("--calibration-seeds", default="2")
    parser.add_argument("--holdout-seeds", default="3")
    parser.add_argument("--gamma-threshold", type=float, default=0.5)
    parser.add_argument("--theta-slack", type=float, default=0.02)
    parser.add_argument("--c-lambda-slack", type=float, default=0.05)
    parser.add_argument("--slope-slack", type=float, default=0.1)
    parser.add_argument("--end-parabolic-time", type=float, default=0.002)
    parser.add_argument("--output-count", type=int, default=3)
    parser.add_argument("--cfl", type=float, default=0.2)
    parser.add_argument("--verify-count", type=int, default=1)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    parameters = packet_parameter_grid(
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
        parameters=parameters,
        center_seeds=parse_int_tuple(args.center_seeds),
        calibration_seeds=parse_int_tuple(args.calibration_seeds),
        holdout_seeds=parse_int_tuple(args.holdout_seeds),
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
                "profile_count": result["profile_count"],
                "fitted_theta": result["fitted_danger_constants"]["fitted_theta"],
                "fitted_c_lambda": result["fitted_danger_constants"]["fitted_c_lambda"],
                "common_member_upper": result["sampled_common_member_upper"],
                "sampled_full_chain_survives": result["authority"][
                    "sampled_full_chain_survives"
                ],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
