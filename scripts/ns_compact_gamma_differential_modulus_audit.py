#!/usr/bin/env python3
"""Exact finite-Galerkin differential audit for compact-Gamma retention.

On the strict positive-transfer branch this computes exact directional
variations of

    Gamma = Q / (2 nu D)

and, away from mechanism sign collisions,

    E = sum_j max(-DB(u)[F_j(u)] / (nu 2^(2K)), 0).

For each mechanism m_j = DB[F_j]/parabolic_rate it uses

    Dm_j[h] = D2B[h,F_j] + DB[DF_j[h]].

Tangents are projected onto fixed target-packet energy and normalized in

    ||h||_XK^2 = ||h||_2^2 + 2^(-2K) ||grad h||_2^2.

Calibration constants are applied unchanged to held-out and matched
N32/N48/N64 profiles. The finite family is a falsification instrument, not a
shell/cutoff-uniform PDE theorem.
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
    normalize_packet_energy,
    packet_parameter_grid,
    parse_float_tuple,
    parse_int_tuple,
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
    nonlinear_tangent_hat,
)
from ns_compact_gamma_replenishment_audit import MECHANISMS, mechanism_accounting
from ns_galerkin_coherence_core import (
    frequency_grid,
    leray_project_hat,
    packet_mask,
    spectral_gradient,
)


def inner_hat(a: np.ndarray, b: np.ndarray, n: int, mask=None, weight=None) -> float:
    product = np.conjugate(a / float(n ** 3)) * (b / float(n ** 3))
    if weight is not None:
        product = product * weight[..., None]
    if mask is not None:
        product = product[mask]
    return float(np.real(np.sum(product)))


def bilinear_nonlinearity(
    left: np.ndarray,
    right: np.ndarray,
    wave: np.ndarray,
    norm_sq: np.ndarray,
    dealias: np.ndarray,
) -> np.ndarray:
    left_x = np.fft.ifftn(left, axes=(0, 1, 2)).real
    grad_right = spectral_gradient(right, wave)
    convection = np.einsum("...j,...ij->...i", left_x, grad_right)
    convection_hat = np.fft.fftn(convection, axes=(0, 1, 2))
    result = -convection_hat
    dot = np.einsum("...i,...i->...", wave, convection_hat)
    nonzero = norm_sq > 0.0
    result[nonzero] += wave[nonzero] * (dot[nonzero] / norm_sq[nonzero])[:, None]
    return result * dealias[..., None]


def prepare(values: dict[str, Any], h: np.ndarray) -> np.ndarray:
    g = values["geometry"]
    h = np.asarray(h, dtype=np.complex128) * g["dealias"][..., None]
    return leray_project_hat(h, g["wave"], g["norm_sq"])


def project_energy_tangent(values: dict[str, Any], h: np.ndarray) -> tuple[np.ndarray, float]:
    g = values["geometry"]
    h = prepare(values, h)
    p = g["packet"]
    u = g["packet_hat"]
    n = int(g["cutoff"])
    denom = inner_hat(u, u, n, p)
    if denom <= 1e-30:
        raise ValueError("zero packet energy")
    coeff = inner_hat(u, h * p[..., None], n, p) / denom
    h = h - coeff * u
    return h, abs(inner_hat(u, h * p[..., None], n, p))


def norm_xk(values: dict[str, Any], h: np.ndarray, shell: int) -> float:
    g = values["geometry"]
    n = int(g["cutoff"])
    return math.sqrt(max(
        inner_hat(h, h, n)
        + float(2 ** (-2 * shell)) * inner_hat(h, h, n, weight=g["norm_sq"]),
        0.0,
    ))


def rational_compact_second_from_variations(
    *, q: float, s: float,
    q_left: float, q_right: float, q_second: float,
    s_left: float, s_right: float, s_second: float,
) -> float:
    """Mixed derivative of B=q/(q+s)."""
    if q <= 0.0 or s <= 0.0:
        raise ValueError("positive compact branch required")
    r = q + s
    first_right = q_right * s - q * s_right
    numerator_dot = (
        q_second * s + q_right * s_left - q_left * s_right - q * s_second
    )
    return (numerator_dot * r - 2.0 * first_right * (q_left + s_left)) / r ** 3


def compact_second(
    values: dict[str, Any], left: np.ndarray, right: np.ndarray, nu: float, shell: int
) -> float:
    g = values["geometry"]
    p = g["packet"]
    selector = p[..., None]
    n = int(g["cutoff"])
    u = g["retained_hat"]
    uk = g["packet_hat"]
    nonlinear = g["nonlinear_packet_hat"]
    left = prepare(values, left)
    right = prepare(values, right)
    lk = left * selector
    rk = right * selector
    nl = nonlinear_tangent_hat(u, left, g["wave"], g["norm_sq"], g["dealias"]) * selector
    nr = nonlinear_tangent_hat(u, right, g["wave"], g["norm_sq"], g["dealias"]) * selector
    nlr = (
        bilinear_nonlinearity(left, right, g["wave"], g["norm_sq"], g["dealias"])
        + bilinear_nonlinearity(right, left, g["wave"], g["norm_sq"], g["dealias"])
    ) * selector
    c = 2.0 * float(2 ** shell)
    ql = c * (inner_hat(lk, nonlinear, n, p) + inner_hat(uk, nl, n, p))
    qr = c * (inner_hat(rk, nonlinear, n, p) + inner_hat(uk, nr, n, p))
    qlr = c * (
        inner_hat(lk, nr, n, p) + inner_hat(rk, nl, n, p) + inner_hat(uk, nlr, n, p)
    )
    dl = 2.0 * inner_hat(uk, lk, n, p, g["norm_sq"])
    dr = 2.0 * inner_hat(uk, rk, n, p, g["norm_sq"])
    dlr = 2.0 * inner_hat(lk, rk, n, p, g["norm_sq"])
    return rational_compact_second_from_variations(
        q=float(values["signed_transfer_Q"]),
        s=float(values["viscous_denominator_2nuD"]),
        q_left=ql, q_right=qr, q_second=qlr,
        s_left=2.0 * nu * dl, s_right=2.0 * nu * dr, s_second=2.0 * nu * dlr,
    )


def mechanism_fields(values: dict[str, Any], h: np.ndarray | None, nu: float) -> dict[str, np.ndarray]:
    g = values["geometry"]
    p = g["packet"]
    if h is None:
        nonlinear = g["components"]["target_advective"] + g["components"]["target_pressure"]
        off = g["components"]["off_packet_advective"] + g["components"]["off_packet_pressure"]
        viscous = g["components"]["target_viscous"] + g["components"]["off_packet_viscous"]
        return {"target_nonlinear": nonlinear, "off_packet_nonlinear": off, "viscous": viscous}
    h = prepare(values, h)
    dn = nonlinear_tangent_hat(g["retained_hat"], h, g["wave"], g["norm_sq"], g["dealias"])
    return {
        "target_nonlinear": dn * p[..., None],
        "off_packet_nonlinear": dn * (~p)[..., None],
        "viscous": -nu * g["norm_sq"][..., None] * h,
    }


def exact_differential(
    raw: np.ndarray,
    h: np.ndarray,
    *, nu: float, shell: int, sign_floor_relative: float = 1e-11,
) -> dict[str, Any]:
    snapshot = compact_gamma_snapshot(raw, nu, shell)
    if snapshot["positive_part_branch"] != "strict_positive_transfer":
        return {"resolved": False, "reason": "positive-transfer-branch", "gamma": snapshot["gamma"]}
    values = {**snapshot, "geometry": _state_geometry(raw, nu, shell)}
    h, tangent_residual = project_energy_tangent(values, h)
    size = norm_xk(values, h, shell)
    if size <= 1e-30:
        return {"resolved": False, "reason": "zero-projected-tangent", "gamma": snapshot["gamma"]}
    h = h / size
    tangent_residual /= size
    gamma_dot = _directional_derivative(values, h, nu, shell)["gamma_derivative"]
    if gamma_dot is None:
        return {"resolved": False, "reason": "gamma-kink", "gamma": snapshot["gamma"]}

    fields = mechanism_fields(values, None, nu)
    dfields = mechanism_fields(values, h, nu)
    signed: dict[str, float] = {}
    dsigned: dict[str, float] = {}
    rate = float(snapshot["parabolic_rate"])
    for name in MECHANISMS:
        first = _directional_derivative(values, fields[name], nu, shell)[
            "compact_gamma_potential_derivative"
        ]
        second = compact_second(values, h, fields[name], nu, shell)
        field_dot = _directional_derivative(values, dfields[name], nu, shell)[
            "compact_gamma_potential_derivative"
        ]
        if first is None or field_dot is None:
            return {"resolved": False, "reason": f"{name}-derivative-kink", "gamma": snapshot["gamma"]}
        signed[name] = float(first) / rate
        dsigned[name] = (second + float(field_dot)) / rate

    floor = sign_floor_relative * max(sum(abs(x) for x in signed.values()), 1.0)
    collisions = [name for name, value in signed.items() if abs(value) <= floor]
    if collisions:
        return {
            "resolved": False,
            "reason": "mechanism-sign-collision",
            "colliding_mechanisms": collisions,
            "gamma": snapshot["gamma"],
        }
    active = [name for name, value in signed.items() if value < 0.0]
    escape = sum(-signed[name] for name in active)
    if escape <= floor:
        return {"resolved": False, "reason": "zero-escape", "gamma": snapshot["gamma"]}
    escape_dot = sum(-dsigned[name] for name in active)
    log_escape_dot = escape_dot / escape

    accounting = mechanism_accounting(snapshot)
    reconstruction = max(
        abs(signed[name] - float(accounting["signed_contributions"][name]))
        for name in MECHANISMS
    )

    raw_norm = float(np.linalg.norm(values["geometry"]["retained_hat"]))
    h_norm = float(np.linalg.norm(h))
    eps = min(1e-5, 2e-7 * max(raw_norm, 1.0) / max(h_norm, 1e-30))
    plus = compact_gamma_snapshot(raw + eps * h, nu, shell)
    minus = compact_gamma_snapshot(raw - eps * h, nu, shell)
    fd_ok = all(x["positive_part_branch"] == "strict_positive_transfer" for x in (plus, minus))
    gamma_fd_residual = None
    log_fd_residual = None
    if fd_ok:
        pa, ma = mechanism_accounting(plus), mechanism_accounting(minus)
        signs = lambda a: tuple(math.copysign(1.0, a["signed_contributions"][n]) for n in MECHANISMS)
        fd_ok = signs(pa) == signs(accounting) == signs(ma)
    if fd_ok:
        gamma_fd = (float(plus["gamma"]) - float(minus["gamma"])) / (2.0 * eps)
        gamma_fd_residual = abs(gamma_fd - float(gamma_dot))
        ep, em = float(mechanism_accounting(plus)["escape_supply"]), float(mechanism_accounting(minus)["escape_supply"])
        if ep > 0.0 and em > 0.0:
            log_fd = (math.log(ep) - math.log(em)) / (2.0 * eps)
            log_fd_residual = abs(log_fd - log_escape_dot)

    return {
        "resolved": True,
        "gamma": float(snapshot["gamma"]),
        "tangent_norm_XK_before_normalization": size,
        "packet_energy_tangent_residual": tangent_residual,
        "gamma_derivative": float(gamma_dot),
        "abs_gamma_derivative": abs(float(gamma_dot)),
        "escape_supply": escape,
        "log_escape_derivative": log_escape_dot,
        "abs_log_escape_derivative": abs(log_escape_dot),
        "signed_mechanisms": signed,
        "signed_mechanism_derivatives": dsigned,
        "minimum_mechanism_sign_distance": min(abs(x) - floor for x in signed.values()),
        "mechanism_reconstruction_residual": reconstruction,
        "gamma_finite_difference_residual": gamma_fd_residual,
        "log_escape_finite_difference_residual": log_fd_residual,
    }


def path_state_tangent(
    center: np.ndarray,
    member: np.ndarray,
    s: float,
    *, nu: float, shell: int, target_energy: float,
) -> tuple[np.ndarray, np.ndarray, float]:
    affine = (1.0 - s) * center + s * member
    direction = member - center
    state, metadata = normalize_packet_energy(affine, shell, target_energy)
    n = int(state.shape[0])
    wave, norm_sq, norm, dealias = frequency_grid(n)
    a = leray_project_hat(affine * dealias[..., None], wave, norm_sq)
    d = leray_project_hat(direction * dealias[..., None], wave, norm_sq)
    p = packet_mask(norm, shell, dealias)
    e = inner_hat(a * p[..., None], a * p[..., None], n, p)
    de = 2.0 * inner_hat(a * p[..., None], d * p[..., None], n, p)
    scale = float(metadata["scale_factor"])
    tangent = scale * d - scale * de / (2.0 * e) * a
    return state, tangent, float(metadata["normalization_residual"])


def dangerous_rows(profile: dict[str, Any], count: int) -> list[dict[str, Any]]:
    rows = [row for row in profile["rows"] if bool(row.get("dangerous", False))]
    return sorted(rows, key=lambda row: float(row["gamma"]), reverse=True)[:count]


def differential_rows(
    profiles: list[dict[str, Any]],
    centers: list[dict[str, Any]],
    trajectories: dict[str, list[dict[str, Any]]],
    *, nu: float, target_energy: float, path_parameters: tuple[float, ...],
    times_per_profile: int, tangent_kinds: tuple[str, ...], sign_floor_relative: float,
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for profile in profiles:
        center, _ = nearest_center(profile, centers)
        shell = int(profile["target_shell"])
        for row in dangerous_rows(profile, times_per_profile):
            tau = float(row["parabolic_time"])
            member_raw = state_at_time(trajectories[profile["profile_id"]], tau)
            center_raw = state_at_time(trajectories[center["profile_id"]], tau)
            for parameter in path_parameters:
                state, path_tangent, normalization_residual = path_state_tangent(
                    center_raw, member_raw, parameter,
                    nu=nu, shell=shell, target_energy=target_energy,
                )
                snapshot = compact_gamma_snapshot(state, nu, shell)
                geometry = _state_geometry(state, nu, shell)
                tangents = {"path": path_tangent, "rhs": geometry["total_rhs_hat"]}
                unknown = set(tangent_kinds) - set(tangents)
                if unknown:
                    raise ValueError(f"unsupported tangent kinds: {sorted(unknown)}")
                for kind in tangent_kinds:
                    output.append({
                        "profile_id": profile["profile_id"],
                        "center_profile_id": center["profile_id"],
                        "cutoff": int(profile["cutoff"]),
                        "target_shell": shell,
                        "parabolic_time": tau,
                        "path_parameter": parameter,
                        "tangent_kind": kind,
                        "path_gamma": float(snapshot["gamma"]),
                        "normalization_residual": normalization_residual,
                        "differential": exact_differential(
                            state, tangents[kind], nu=nu, shell=shell,
                            sign_floor_relative=sign_floor_relative,
                        ),
                    })
    return output


def fit_constants(rows: list[dict[str, Any]], *, slack: float) -> dict[str, Any]:
    resolved = [row for row in rows if row["differential"]["resolved"]]
    unresolved = [row for row in rows if not row["differential"]["resolved"]]
    gamma = [float(row["differential"]["abs_gamma_derivative"]) for row in resolved]
    loge = [float(row["differential"]["abs_log_escape_derivative"]) for row in resolved]
    finite = bool(resolved) and not unresolved and all(math.isfinite(x) for x in gamma + loge)
    return {
        "row_count": len(rows),
        "resolved_row_count": len(resolved),
        "unresolved_row_count": len(unresolved),
        "unresolved_reasons": sorted({row["differential"].get("reason") for row in unresolved}),
        "raw_gamma_constant": max(gamma, default=None),
        "raw_log_escape_constant": max(loge, default=None),
        "fitted_gamma_constant": max(gamma, default=math.inf) * (1.0 + slack) if finite else math.inf,
        "fitted_log_escape_constant": max(loge, default=math.inf) * (1.0 + slack) if finite else math.inf,
        "slack": slack,
        "finite_candidate": finite,
    }


def evaluate_rows(rows: list[dict[str, Any]], *, gamma_constant: float, log_constant: float) -> dict[str, Any]:
    evaluated: list[dict[str, Any]] = []
    for row in rows:
        d = row["differential"]
        base = {k: row[k] for k in (
            "profile_id", "cutoff", "target_shell", "parabolic_time", "path_parameter", "tangent_kind"
        )}
        if not d["resolved"]:
            evaluated.append({**base, "resolved": False, "survives": False, "reason": d.get("reason")})
            continue
        gm = gamma_constant - float(d["abs_gamma_derivative"])
        lm = log_constant - float(d["abs_log_escape_derivative"])
        evaluated.append({
            **base, "resolved": True,
            "gamma_derivative": float(d["abs_gamma_derivative"]),
            "log_escape_derivative": float(d["abs_log_escape_derivative"]),
            "gamma_margin": gm, "log_escape_margin": lm,
            "survives": gm >= -1e-10 and lm >= -1e-10,
        })
    resolved = [row for row in evaluated if row["resolved"]]
    return {
        "row_count": len(evaluated),
        "resolved_row_count": len(resolved),
        "unresolved_row_count": len(evaluated) - len(resolved),
        "minimum_gamma_margin": min((row["gamma_margin"] for row in resolved), default=None),
        "minimum_log_escape_margin": min((row["log_escape_margin"] for row in resolved), default=None),
        "sampled_differential_modulus_survives": bool(evaluated) and all(row["survives"] for row in evaluated),
        "rows": evaluated,
    }


def exact_matched_profile(source: dict[str, Any], split: str, cutoff: int, **kwargs) -> dict[str, Any]:
    parameters = PacketParameters(**source["parameters"])
    profile = build_profile(
        split=split, seed=int(source["derived_state_seed"]), parameters=parameters,
        cutoff=cutoff, target_shell=int(source["target_shell"]), **kwargs,
    )
    profile["base_parameters"] = asdict(parameters)
    profile["perturbation_sample_index"] = 0
    profile["derived_state_seed"] = int(source["derived_state_seed"])
    return profile


def audit_family(
    *, search_cutoff: int, verify_cutoffs: tuple[int, ...], target_shells: tuple[int, ...],
    nu: float, input_amplitude: float, target_packet_energy: float,
    base_parameters: tuple[PacketParameters, ...], center_seeds: tuple[int, ...],
    calibration_seeds: tuple[int, ...], holdout_seeds: tuple[int, ...],
    samples_per_base: int, phase_jitter: float, log_ratio_jitter: float,
    log_satellite_jitter: float, gamma_threshold: float,
    path_parameters: tuple[float, ...], tangent_kinds: tuple[str, ...],
    times_per_profile: int, differential_slack: float, sign_floor_relative: float,
    end_parabolic_time: float, output_count: int, cfl: float, verify_count: int,
) -> dict[str, Any]:
    centers, calibration, holdout = build_profile_sets(
        base_parameters=base_parameters, center_seeds=center_seeds,
        calibration_seeds=calibration_seeds, holdout_seeds=holdout_seeds,
        samples_per_base=samples_per_base, calibration_jitter_scale=1.0,
        holdout_jitter_scale=1.0, phase_jitter=phase_jitter,
        log_ratio_jitter=log_ratio_jitter, log_satellite_jitter=log_satellite_jitter,
        cutoff=search_cutoff, target_shells=target_shells, nu=nu,
        input_amplitude=input_amplitude, target_packet_energy=target_packet_energy,
        gamma_threshold=gamma_threshold, end_parabolic_time=end_parabolic_time,
        output_count=output_count, cfl=cfl,
    )
    common = dict(
        nu=nu, input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy,
        end_parabolic_time=end_parabolic_time, output_count=output_count, cfl=cfl,
    )
    trajectories = {p["profile_id"]: reconstruct_trajectory(p, **common) for p in centers + calibration + holdout}
    calibration_rows = differential_rows(
        calibration, centers, trajectories, nu=nu, target_energy=target_packet_energy,
        path_parameters=path_parameters, times_per_profile=times_per_profile,
        tangent_kinds=tangent_kinds, sign_floor_relative=sign_floor_relative,
    )
    holdout_rows = differential_rows(
        holdout, centers, trajectories, nu=nu, target_energy=target_packet_energy,
        path_parameters=path_parameters, times_per_profile=times_per_profile,
        tangent_kinds=tangent_kinds, sign_floor_relative=sign_floor_relative,
    )
    fitted = fit_constants(calibration_rows, slack=differential_slack)
    holdout_eval = evaluate_rows(
        holdout_rows, gamma_constant=float(fitted["fitted_gamma_constant"]),
        log_constant=float(fitted["fitted_log_escape_constant"]),
    )

    selected: list[dict[str, Any]] = []
    for shell in target_shells:
        candidates = [p for p in holdout if int(p["target_shell"]) == shell]
        candidates.sort(key=lambda p: -max(float(r["gamma"]) for r in p["rows"]))
        selected.extend(candidates[:verify_count])
    matched_rows: list[dict[str, Any]] = []
    matched_profile_count = 0
    build_kwargs = dict(
        nu=nu, input_amplitude=input_amplitude,
        target_packet_energy=target_packet_energy, gamma_threshold=gamma_threshold,
        end_parabolic_time=end_parabolic_time, output_count=output_count, cfl=cfl,
    )
    for member_source in selected:
        center_source, _ = nearest_center(member_source, centers)
        for cutoff in verify_cutoffs:
            member = exact_matched_profile(member_source, "matched-member", cutoff, **build_kwargs)
            center = exact_matched_profile(center_source, "matched-center", cutoff, **build_kwargs)
            matched_profile_count += 1
            local = {p["profile_id"]: reconstruct_trajectory(p, **common) for p in (member, center)}
            matched_rows.extend(differential_rows(
                [member], [center], local, nu=nu, target_energy=target_packet_energy,
                path_parameters=path_parameters, times_per_profile=times_per_profile,
                tangent_kinds=tangent_kinds, sign_floor_relative=sign_floor_relative,
            ))
    matched_eval = evaluate_rows(
        matched_rows, gamma_constant=float(fitted["fitted_gamma_constant"]),
        log_constant=float(fitted["fitted_log_escape_constant"]),
    )

    group_map: dict[tuple[int, float, float, str], list[dict[str, Any]]] = {}
    for row in matched_eval["rows"]:
        if row["resolved"]:
            key = (int(row["target_shell"]), float(row["parabolic_time"]), float(row["path_parameter"]), str(row["tangent_kind"]))
            group_map.setdefault(key, []).append(row)
    groups = []
    for key, rows in sorted(group_map.items()):
        cutoffs = sorted({int(row["cutoff"]) for row in rows})
        gv = [float(row["gamma_derivative"]) for row in rows]
        lv = [float(row["log_escape_derivative"]) for row in rows]
        groups.append({
            "target_shell": key[0], "parabolic_time": key[1],
            "path_parameter": key[2], "tangent_kind": key[3],
            "observed_cutoffs": cutoffs,
            "matched_cutoff_complete": set(cutoffs) == set(verify_cutoffs),
            "gamma_derivative_spread": max(gv) - min(gv),
            "log_escape_derivative_spread": max(lv) - min(lv),
        })

    all_rows = calibration_rows + holdout_rows + matched_rows
    resolved = [row["differential"] for row in all_rows if row["differential"]["resolved"]]
    finite_values = lambda key: [float(d[key]) for d in resolved if d[key] is not None]
    full = (
        bool(fitted["finite_candidate"])
        and bool(holdout_eval["sampled_differential_modulus_survives"])
        and bool(matched_eval["sampled_differential_modulus_survives"])
        and bool(groups) and all(g["matched_cutoff_complete"] for g in groups)
    )
    return {
        "schema_version": "1.0.0",
        "authority": {
            "exact_finite_galerkin_gamma_directional_derivative": True,
            "exact_finite_galerkin_escape_directional_derivative_away_from_sign_kinks": True,
            "sampled_differential_modulus_survives_holdout": bool(holdout_eval["sampled_differential_modulus_survives"]),
            "sampled_differential_modulus_survives_matched_cutoffs": bool(matched_eval["sampled_differential_modulus_survives"]),
            "sampled_full_differential_chain_survives": full,
            "analytic_cutoff_shell_uniform_gamma_modulus_proved": False,
            "analytic_cutoff_shell_uniform_log_escape_modulus_proved": False,
            "compact_path_coverage_proved": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "parameters": {
            "search_cutoff": search_cutoff, "verify_cutoffs": list(verify_cutoffs),
            "target_shells": list(target_shells), "path_parameters": list(path_parameters),
            "tangent_kinds": list(tangent_kinds), "times_per_profile": times_per_profile,
            "target_packet_energy": target_packet_energy,
        },
        "center_profile_count": len(centers),
        "calibration_profile_count": len(calibration),
        "holdout_profile_count": len(holdout),
        "calibration_row_count": len(calibration_rows),
        "holdout_row_count": len(holdout_rows),
        "matched_profile_count": matched_profile_count,
        "matched_row_count": len(matched_rows),
        "fitted_differential_constants": fitted,
        "holdout_evaluation": holdout_eval,
        "matched_evaluation": matched_eval,
        "matched_cutoff_groups": groups,
        "maximum_matched_gamma_derivative_spread": max((g["gamma_derivative_spread"] for g in groups), default=None),
        "maximum_matched_log_escape_derivative_spread": max((g["log_escape_derivative_spread"] for g in groups), default=None),
        "maximum_gamma_finite_difference_residual": max(finite_values("gamma_finite_difference_residual"), default=None),
        "maximum_log_escape_finite_difference_residual": max(finite_values("log_escape_finite_difference_residual"), default=None),
        "maximum_mechanism_reconstruction_residual": max(finite_values("mechanism_reconstruction_residual"), default=None),
        "maximum_packet_energy_tangent_residual": max(finite_values("packet_energy_tangent_residual"), default=None),
        "calibration_rows": calibration_rows,
        "holdout_rows": holdout_rows,
        "matched_rows": matched_rows,
        "limitations": [
            "finite selected tangent family", "mechanism sign collisions fail closed",
            "fitted rather than analytic constants", "no shell/cutoff uniform theorem",
            "no compact path coverage, BKM, global regularity, or Clay promotion",
        ],
    }


def parse_strings(raw: str) -> tuple[str, ...]:
    result = tuple(x.strip() for x in raw.split(",") if x.strip())
    if not result:
        raise ValueError("empty string tuple")
    return result


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output-json", type=Path, required=True)
    p.add_argument("--search-cutoff", type=int, default=24)
    p.add_argument("--verify-cutoffs", default="32,48,64")
    p.add_argument("--target-shells", default="2,3")
    p.add_argument("--viscosity", type=float, default=0.01)
    p.add_argument("--input-amplitude", type=float, default=0.1)
    p.add_argument("--target-packet-energy", type=float, default=0.86)
    p.add_argument("--triad-counts", default="4")
    p.add_argument("--phase-spreads", default="0.0,0.5")
    p.add_argument("--target-ratios", default="1.25,2.5")
    p.add_argument("--satellite-fractions", default="0.55")
    p.add_argument("--center-seeds", default="1")
    p.add_argument("--calibration-seeds", default="2")
    p.add_argument("--holdout-seeds", default="3")
    p.add_argument("--samples-per-base", type=int, default=1)
    p.add_argument("--phase-jitter", type=float, default=0.8)
    p.add_argument("--log-ratio-jitter", type=float, default=0.5)
    p.add_argument("--log-satellite-jitter", type=float, default=0.35)
    p.add_argument("--gamma-threshold", type=float, default=0.5)
    p.add_argument("--path-parameters", default="0.0,0.5,1.0")
    p.add_argument("--tangent-kinds", default="path,rhs")
    p.add_argument("--times-per-profile", type=int, default=1)
    p.add_argument("--differential-slack", type=float, default=0.25)
    p.add_argument("--mechanism-relative-floor", type=float, default=1e-11)
    p.add_argument("--end-parabolic-time", type=float, default=0.004)
    p.add_argument("--output-count", type=int, default=3)
    p.add_argument("--cfl", type=float, default=0.2)
    p.add_argument("--verify-count", type=int, default=1)
    p.add_argument("--pretty", action="store_true")
    a = p.parse_args()
    result = audit_family(
        search_cutoff=a.search_cutoff, verify_cutoffs=parse_int_tuple(a.verify_cutoffs),
        target_shells=parse_int_tuple(a.target_shells), nu=a.viscosity,
        input_amplitude=a.input_amplitude, target_packet_energy=a.target_packet_energy,
        base_parameters=packet_parameter_grid(
            parse_int_tuple(a.triad_counts), parse_float_tuple(a.phase_spreads),
            parse_float_tuple(a.target_ratios), parse_float_tuple(a.satellite_fractions),
        ),
        center_seeds=parse_int_tuple(a.center_seeds),
        calibration_seeds=parse_int_tuple(a.calibration_seeds),
        holdout_seeds=parse_int_tuple(a.holdout_seeds),
        samples_per_base=a.samples_per_base, phase_jitter=a.phase_jitter,
        log_ratio_jitter=a.log_ratio_jitter, log_satellite_jitter=a.log_satellite_jitter,
        gamma_threshold=a.gamma_threshold, path_parameters=parse_float_tuple(a.path_parameters),
        tangent_kinds=parse_strings(a.tangent_kinds), times_per_profile=a.times_per_profile,
        differential_slack=a.differential_slack,
        sign_floor_relative=a.mechanism_relative_floor,
        end_parabolic_time=a.end_parabolic_time, output_count=a.output_count,
        cfl=a.cfl, verify_count=a.verify_count,
    )
    atomic_json(a.output_json, result, a.pretty)
    print(json.dumps({
        "output_json": str(a.output_json),
        "fitted": result["fitted_differential_constants"],
        "holdout_survives": result["authority"]["sampled_differential_modulus_survives_holdout"],
        "matched_survives": result["authority"]["sampled_differential_modulus_survives_matched_cutoffs"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
