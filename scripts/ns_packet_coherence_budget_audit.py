#!/usr/bin/env python3
"""Audit packet eigenframe coherence and candidate depletion budgets.

The input is the JSON produced by ``ns_shell_angle_residence_audit.py``. For
all available ``raw_hat`` checkpoints this program reconstructs the dealiased
velocity gradient, target-shell vorticity/strain eigenframe, the pressure
Hessian, middle-eigenvalue branches, and a rotationally invariant quasi-2D
planarity defect.

The resulting finite-difference budget rows are hypothesis-discovery objects:
they test candidate inequalities of the form

    d A_K / d tau + kappa 1_{Gamma_K >= lambda} <= R_K,

where ``tau = nu 2^(2K) t`` and ``A_K`` is the packet-enstrophy-weighted top
strain-eigenvector alignment. No interpolation between checkpoints or
cutoff-uniform theorem is inferred.
"""
from __future__ import annotations

import argparse
import json
import math
import os
from dataclasses import dataclass
from pathlib import Path
import tempfile
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_packet_coherence_budget_audit.py"


def parse_float_list(raw: str, *, nonnegative: bool = True) -> tuple[float, ...]:
    values = tuple(sorted({float(token.strip()) for token in raw.split(",") if token.strip()}))
    if not values or any(not math.isfinite(value) for value in values):
        raise ValueError("expected a nonempty finite float list")
    if nonnegative and any(value < 0.0 for value in values):
        raise ValueError("values must be nonnegative")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--residence-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--gamma-thresholds", default="0.5,0.9,1.0")
    parser.add_argument("--kappa-candidates", default="0.01,0.05,0.1,0.25")
    parser.add_argument("--middle-alpha-threshold", type=float, default=0.2)
    parser.add_argument("--gap-relative-floor", type=float, default=1.0e-6)
    parser.add_argument("--pressure-remainder-coefficient", type=float, default=1.0)
    parser.add_argument("--tail-remainder-coefficient", type=float, default=1.0)
    parser.add_argument("--middle-remainder-coefficient", type=float, default=1.0)
    parser.add_argument("--allow-missing-state", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def atomic_json(path: Path, payload: dict[str, Any], pretty: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent,
        prefix=f".{path.name}.", suffix=".partial", delete=False,
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


def frequency_grid(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    axis = np.fft.fftfreq(n) * n
    kz, ky, kx = np.meshgrid(axis, axis, axis, indexing="ij")
    wave = np.stack((kx, ky, kz), axis=-1)
    norm_sq = np.sum(wave * wave, axis=-1)
    dealias = np.all(np.abs(wave) <= float(n) / 3.0, axis=-1)
    return wave, norm_sq, dealias


def spectral_gradient(hat: np.ndarray, wave: np.ndarray) -> np.ndarray:
    """Return G[..., i, j] = partial_j u_i from an FFT coefficient array."""
    if hat.ndim != 4 or hat.shape[-1] != 3:
        raise ValueError("hat must have shape (N,N,N,3)")
    grad = np.empty(hat.shape[:3] + (3, 3), dtype=np.float64)
    for component in range(3):
        for derivative in range(3):
            grad[..., component, derivative] = np.fft.ifftn(
                1j * wave[..., derivative] * hat[..., component], axes=(0, 1, 2)
            ).real
    return grad


def curl_from_gradient(grad: np.ndarray) -> np.ndarray:
    omega = np.empty(grad.shape[:-2] + (3,), dtype=np.float64)
    omega[..., 0] = grad[..., 2, 1] - grad[..., 1, 2]
    omega[..., 1] = grad[..., 0, 2] - grad[..., 2, 0]
    omega[..., 2] = grad[..., 1, 0] - grad[..., 0, 1]
    return omega


def strain_from_gradient(grad: np.ndarray) -> np.ndarray:
    return 0.5 * (grad + np.swapaxes(grad, -1, -2))


def pressure_hessian_from_gradient(grad: np.ndarray, wave: np.ndarray, norm_sq: np.ndarray) -> np.ndarray:
    """Solve Delta p = -partial_i u_j partial_j u_i and return Hess p."""
    quadratic = np.einsum("...ij,...ji->...", grad, grad)
    quadratic_hat = np.fft.fftn(quadratic, axes=(0, 1, 2))
    pressure_hat = np.zeros_like(quadratic_hat, dtype=np.complex128)
    nonzero = norm_sq > 0.0
    pressure_hat[nonzero] = quadratic_hat[nonzero] / norm_sq[nonzero]
    hessian = np.empty(grad.shape, dtype=np.float64)
    for left in range(3):
        for right in range(3):
            hessian[..., left, right] = np.fft.ifftn(
                -wave[..., left] * wave[..., right] * pressure_hat,
                axes=(0, 1, 2),
            ).real
    return hessian


def weighted_mean(values: np.ndarray, weights: np.ndarray) -> float:
    denominator = float(np.sum(weights))
    if denominator <= 0.0:
        return 0.0
    return float(np.sum(values * weights) / denominator)


def weighted_fraction(mask: np.ndarray, weights: np.ndarray) -> float:
    denominator = float(np.sum(weights))
    if denominator <= 0.0:
        return 0.0
    return float(np.sum(weights[mask]) / denominator)


def eigenframe_metrics(
    packet_gradient: np.ndarray,
    full_pressure_hessian: np.ndarray,
    *,
    nu: float,
    target_shell: int,
    middle_alpha_threshold: float,
    gap_relative_floor: float,
) -> dict[str, Any]:
    strain = strain_from_gradient(packet_gradient)
    omega = curl_from_gradient(packet_gradient)
    omega_sq = np.sum(omega * omega, axis=-1)
    maximum_omega_sq = float(np.max(omega_sq)) if omega_sq.size else 0.0
    active = omega_sq > max(1.0e-30, 1.0e-12 * maximum_omega_sq)
    weights = np.where(active, omega_sq, 0.0)
    total_enstrophy = float(np.sum(weights))
    if total_enstrophy <= 0.0:
        raise ValueError("target packet has zero resolved enstrophy")

    eigenvalues, eigenvectors = np.linalg.eigh(strain)
    eigenvalues = eigenvalues[..., ::-1]
    eigenvectors = eigenvectors[..., :, ::-1]

    xi = np.zeros_like(omega)
    xi[active] = omega[active] / np.sqrt(omega_sq[active])[:, None]
    projections = np.einsum("...ji,...j->...i", eigenvectors, xi)
    alpha = projections * projections
    sigma_from_frame = np.sum(eigenvalues * alpha, axis=-1)
    sigma_direct = np.einsum("...i,...ij,...j->...", xi, strain, xi)
    identity_residual = np.abs(sigma_from_frame - sigma_direct)

    hessian_trace = np.trace(full_pressure_hessian, axis1=-2, axis2=-1)
    identity = np.eye(3, dtype=np.float64)
    hessian_tf = full_pressure_hessian - hessian_trace[..., None, None] * identity / 3.0
    e1 = eigenvectors[..., :, 0]
    e2 = eigenvectors[..., :, 1]
    pressure_mix_21 = np.einsum("...i,...ij,...j->...", e2, hessian_tf, e1)
    strain_scale = np.sqrt(np.sum(eigenvalues * eigenvalues, axis=-1))
    gap12 = np.maximum(eigenvalues[..., 0] - eigenvalues[..., 1], 0.0)
    gap_denominator = np.maximum(gap12, gap_relative_floor * strain_scale + 1.0e-30)
    pressure_rotation_21 = pressure_mix_21 / gap_denominator

    sxi = np.einsum("...ij,...j->...i", strain, xi)
    kinematic_turnover = np.linalg.norm(sxi - sigma_direct[..., None] * xi, axis=-1)

    singular_values = np.linalg.svd(packet_gradient, compute_uv=False)
    gradient_sq = np.sum(singular_values * singular_values, axis=-1)
    planarity_defect = np.divide(
        singular_values[..., -1] ** 2,
        gradient_sq,
        out=np.zeros_like(gradient_sq),
        where=gradient_sq > 1.0e-30,
    )

    lambda2 = eigenvalues[..., 1]
    alpha2 = alpha[..., 1]
    branch1 = lambda2 <= 0.0
    branch2 = (lambda2 > 0.0) & (alpha2 < middle_alpha_threshold)
    branch3 = (lambda2 > 0.0) & (alpha2 >= middle_alpha_threshold)

    parabolic_rate = nu * float(2 ** (2 * target_shell))
    pressure_rotation_normalized = pressure_rotation_21 / parabolic_rate
    kinematic_turnover_normalized = kinematic_turnover / parabolic_rate

    positive_stretch = np.maximum(sigma_from_frame, 0.0)
    positive_middle_channel = np.maximum(lambda2 * alpha2, 0.0)
    positive_total = float(np.sum(weights * positive_stretch))
    middle_positive = float(np.sum(weights * positive_middle_channel))

    return {
        "packet_enstrophy_sum": total_enstrophy,
        "active_grid_fraction": float(np.mean(active)),
        "coherence_budget_A1": weighted_mean(alpha[..., 0], weights),
        "middle_alignment_A2": weighted_mean(alpha2, weights),
        "minimum_alignment_A3": weighted_mean(alpha[..., 2], weights),
        "alignment_partition_residual": abs(weighted_mean(np.sum(alpha, axis=-1), weights) - 1.0),
        "effective_stretching_sigma": weighted_mean(sigma_from_frame, weights),
        "positive_effective_stretching": weighted_mean(positive_stretch, weights),
        "eigenframe_stretching_identity_max_residual": float(np.max(identity_residual[active])),
        "lambda1_weighted_mean": weighted_mean(eigenvalues[..., 0], weights),
        "lambda2_weighted_mean": weighted_mean(lambda2, weights),
        "lambda3_weighted_mean": weighted_mean(eigenvalues[..., 2], weights),
        "lambda_trace_weighted_residual": abs(weighted_mean(np.sum(eigenvalues, axis=-1), weights)),
        "lambda2_positive_enstrophy_fraction": weighted_fraction(lambda2 > 0.0, weights),
        "positive_middle_channel_fraction_of_positive_stretching": (
            middle_positive / positive_total if positive_total > 0.0 else None
        ),
        "branch_fractions": {
            "biaxial_lambda2_nonpositive": weighted_fraction(branch1, weights),
            "lambda2_positive_middle_alignment_small": weighted_fraction(branch2, weights),
            "lambda2_positive_middle_alignment_substantial": weighted_fraction(branch3, weights),
            "middle_alpha_threshold": middle_alpha_threshold,
        },
        "pressure_hessian": {
            "trace_free_projection_weighted_trace_residual": abs(weighted_mean(np.trace(hessian_tf, axis1=-2, axis2=-1), weights)),
            "mix_21_weighted_mean": weighted_mean(pressure_mix_21, weights),
            "mix_21_weighted_absolute_mean": weighted_mean(np.abs(pressure_mix_21), weights),
            "eigenframe_rotation_21_weighted_mean": weighted_mean(pressure_rotation_21, weights),
            "eigenframe_rotation_21_positive_parabolic_normalized": weighted_mean(
                np.maximum(pressure_rotation_normalized, 0.0), weights
            ),
            "eigenframe_rotation_21_absolute_parabolic_normalized": weighted_mean(
                np.abs(pressure_rotation_normalized), weights
            ),
            "gap_relative_floor": gap_relative_floor,
        },
        "kinematic_turnover_parabolic_normalized": weighted_mean(kinematic_turnover_normalized, weights),
        "quasi_2d_planarity_defect": {
            "weighted_mean": weighted_mean(planarity_defect, weights),
            "weighted_rms": math.sqrt(weighted_mean(planarity_defect * planarity_defect, weights)),
            "near_columnar_enstrophy_fraction_1e-6": weighted_fraction(planarity_defect <= 1.0e-6, weights),
            "strongly_3d_enstrophy_fraction_1e-2": weighted_fraction(planarity_defect >= 1.0e-2, weights),
        },
    }


def checkpoint_metrics(
    state_path: Path,
    target_shell: int,
    *,
    middle_alpha_threshold: float,
    gap_relative_floor: float,
) -> dict[str, Any]:
    with np.load(state_path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        nu = float(data["nu"]) if "nu" in data else 1.0e-3
    if raw.ndim != 4 or raw.shape[-1] != 3 or len(set(raw.shape[:3])) != 1:
        raise ValueError(f"{state_path}: expected raw_hat shape (N,N,N,3), got {raw.shape!r}")
    if nu <= 0.0:
        raise ValueError("viscosity must be positive")

    n = int(raw.shape[0])
    wave, norm_sq, dealias = frequency_grid(n)
    norm = np.sqrt(norm_sq)
    packet = (
        (norm >= float(2 ** target_shell))
        & (norm < float(2 ** (target_shell + 1)))
        & dealias
    )
    dealiased_hat = raw * dealias[..., None]
    packet_hat = raw * packet[..., None]
    full_gradient = spectral_gradient(dealiased_hat, wave)
    packet_gradient = spectral_gradient(packet_hat, wave)
    pressure_hessian = pressure_hessian_from_gradient(full_gradient, wave, norm_sq)
    metrics = eigenframe_metrics(
        packet_gradient,
        pressure_hessian,
        nu=nu,
        target_shell=target_shell,
        middle_alpha_threshold=middle_alpha_threshold,
        gap_relative_floor=gap_relative_floor,
    )
    metrics.update({
        "cutoff": n,
        "physical_viscosity": nu,
        "target_shell": target_shell,
        "parabolic_rate": nu * float(2 ** (2 * target_shell)),
    })
    return metrics


@dataclass(frozen=True)
class BudgetPoint:
    trajectory_id: str
    checkpoint_index: int
    cutoff: int
    target_shell: int
    time: float
    parabolic_duration: float
    gamma: float | None
    tight: bool
    tail_mass: float
    coherence: float
    pressure_positive: float
    branch3: float


def candidate_remainder(point: BudgetPoint, pressure_coefficient: float,
                        tail_coefficient: float, middle_coefficient: float) -> float:
    return (
        pressure_coefficient * point.pressure_positive
        + tail_coefficient * point.tail_mass
        + middle_coefficient * point.branch3
    )


def budget_intervals(
    points: list[BudgetPoint],
    thresholds: tuple[float, ...],
    kappas: tuple[float, ...],
    *,
    pressure_coefficient: float,
    tail_coefficient: float,
    middle_coefficient: float,
) -> list[dict[str, Any]]:
    points = sorted(points, key=lambda point: (point.trajectory_id, point.time, point.checkpoint_index))
    by_trajectory: dict[str, list[BudgetPoint]] = {}
    for point in points:
        by_trajectory.setdefault(point.trajectory_id, []).append(point)

    audits: list[dict[str, Any]] = []
    for trajectory_id, trajectory in sorted(by_trajectory.items()):
        interval_rows: list[dict[str, Any]] = []
        for current, following in zip(trajectory, trajectory[1:]):
            dtau = current.parabolic_duration
            if dtau <= 0.0:
                continue
            derivative = (following.coherence - current.coherence) / dtau
            interval_rows.append({
                "from_checkpoint": current.checkpoint_index,
                "to_checkpoint": following.checkpoint_index,
                "cutoff": current.cutoff,
                "target_shell": current.target_shell,
                "parabolic_duration": dtau,
                "coherence_A1_start": current.coherence,
                "coherence_A1_end": following.coherence,
                "dA1_dparabolic_time": derivative,
                "gamma_start": current.gamma,
                "packet_tight_start": current.tight,
                "candidate_remainder_components": {
                    "pressure_positive": current.pressure_positive,
                    "tail_mass": current.tail_mass,
                    "branch3_middle_leak": current.branch3,
                },
                "candidate_remainder": candidate_remainder(
                    current, pressure_coefficient, tail_coefficient, middle_coefficient
                ),
            })

        parameter_audits: list[dict[str, Any]] = []
        for threshold in thresholds:
            for kappa in kappas:
                tested = 0
                satisfied = 0
                integrated_required_positive = 0.0
                integrated_candidate = 0.0
                largest_deficit = 0.0
                dangerous_tau = 0.0
                for row in interval_rows:
                    gamma = row["gamma_start"]
                    eligible = bool(row["packet_tight_start"]) and gamma is not None and math.isfinite(float(gamma))
                    if not eligible:
                        continue
                    tested += 1
                    dangerous = float(gamma) >= threshold
                    if dangerous:
                        dangerous_tau += float(row["parabolic_duration"])
                    required = float(row["dA1_dparabolic_time"]) + (kappa if dangerous else 0.0)
                    required_positive = max(required, 0.0)
                    candidate = float(row["candidate_remainder"])
                    duration = float(row["parabolic_duration"])
                    integrated_required_positive += required_positive * duration
                    integrated_candidate += candidate * duration
                    deficit = required_positive - candidate
                    largest_deficit = max(largest_deficit, deficit)
                    if deficit <= 1.0e-12:
                        satisfied += 1
                parameter_audits.append({
                    "gamma_threshold": threshold,
                    "kappa": kappa,
                    "tested_interval_count": tested,
                    "candidate_inequality_satisfied_count": satisfied,
                    "candidate_inequality_satisfied_fraction": satisfied / tested if tested else None,
                    "dangerous_parabolic_residence": dangerous_tau,
                    "integrated_required_positive_remainder": integrated_required_positive,
                    "integrated_candidate_remainder": integrated_candidate,
                    "largest_pointwise_candidate_deficit": largest_deficit,
                })
        audits.append({
            "trajectory_id": trajectory_id,
            "intervals": interval_rows,
            "parameter_audits": parameter_audits,
        })
    return audits


def audit(
    residence_payload: dict[str, Any],
    thresholds: tuple[float, ...],
    kappas: tuple[float, ...],
    *,
    middle_alpha_threshold: float,
    gap_relative_floor: float,
    pressure_coefficient: float,
    tail_coefficient: float,
    middle_coefficient: float,
    allow_missing_state: bool,
) -> dict[str, Any]:
    checkpoints = residence_payload.get("checkpoints")
    if not isinstance(checkpoints, list) or not checkpoints:
        raise ValueError("residence JSON has no nonempty checkpoints list")
    if not (0.0 <= middle_alpha_threshold <= 1.0):
        raise ValueError("middle-alpha-threshold must lie in [0,1]")
    if gap_relative_floor <= 0.0:
        raise ValueError("gap-relative-floor must be positive")
    coefficients = (pressure_coefficient, tail_coefficient, middle_coefficient)
    if any(not math.isfinite(value) or value < 0.0 for value in coefficients):
        raise ValueError("candidate remainder coefficients must be finite and nonnegative")

    rows: list[dict[str, Any]] = []
    points: list[BudgetPoint] = []
    for position, checkpoint in enumerate(checkpoints):
        if not isinstance(checkpoint, dict):
            raise ValueError("checkpoint rows must be objects")
        state_path = Path(str(checkpoint.get("source_state", "")))
        target_shell = int(checkpoint["target_shell"])
        try:
            metrics = checkpoint_metrics(
                state_path,
                target_shell,
                middle_alpha_threshold=middle_alpha_threshold,
                gap_relative_floor=gap_relative_floor,
            )
        except (FileNotFoundError, KeyError, ValueError) as exc:
            if not allow_missing_state:
                raise
            metrics = None
            state_error = str(exc)
        else:
            state_error = None

        row = dict(checkpoint)
        row["coherence_metrics"] = metrics
        row["coherence_available"] = metrics is not None
        row["coherence_state_error"] = state_error
        row["truth_authority"] = False
        row["theorem_authority"] = False
        row["promoted"] = False
        rows.append(row)

        if metrics is None:
            continue
        geometry = checkpoint.get("packet_geometry", {})
        tightness = float(geometry.get("local_shell_mass_fraction", 0.0))
        branch3 = float(metrics["branch_fractions"]["lambda2_positive_middle_alignment_substantial"])
        pressure_positive = float(metrics["pressure_hessian"]["eigenframe_rotation_21_positive_parabolic_normalized"])
        points.append(BudgetPoint(
            trajectory_id=str(checkpoint.get("trajectory_id", "aggregate-trajectory")),
            checkpoint_index=int(checkpoint.get("checkpoint_index", position)),
            cutoff=int(metrics["cutoff"]),
            target_shell=target_shell,
            time=float(checkpoint.get("time", position)),
            parabolic_duration=float(checkpoint.get("parabolic_duration", 0.0)),
            gamma=float(checkpoint["gamma"]) if checkpoint.get("gamma") is not None else None,
            tight=bool(checkpoint.get("packet_tight", False)),
            tail_mass=max(1.0 - tightness, 0.0),
            coherence=float(metrics["coherence_budget_A1"]),
            pressure_positive=pressure_positive,
            branch3=branch3,
        ))

    cutoff_groups: dict[tuple[int, int], list[BudgetPoint]] = {}
    for point in points:
        cutoff_groups.setdefault((point.cutoff, point.target_shell), []).append(point)
    cutoff_summary = [
        {
            "cutoff": cutoff,
            "target_shell": target_shell,
            "checkpoint_count": len(group),
            "maximum_coherence_budget_A1": max(point.coherence for point in group),
            "maximum_pressure_positive_parabolic_normalized": max(point.pressure_positive for point in group),
            "maximum_branch3_middle_leak_fraction": max(point.branch3 for point in group),
            "maximum_tail_mass": max(point.tail_mass for point in group),
        }
        for (cutoff, target_shell), group in sorted(cutoff_groups.items())
    ]

    return {
        "schema_version": "1.0.0",
        "script": SCRIPT_NAME,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "pressure_hessian_sign_authority": False,
            "cutoff_uniform_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "coherence_budget_A1": "packet-enstrophy weighted (xi dot e1)^2",
            "middle_alignment_A2": "packet-enstrophy weighted (xi dot e2)^2",
            "pressure_rotation_21": "(e2 dot Hess(p)_tf e1)/(lambda1-lambda2) with relative gap floor",
            "quasi_2d_planarity_defect": "smallest singular value squared of packet gradient divided by Frobenius norm squared",
            "branch_I": "lambda2 <= 0",
            "branch_II": "lambda2 > 0 and alpha2 below threshold",
            "branch_III": "lambda2 > 0 and alpha2 at least threshold",
            "candidate_budget": "dA1/dtau + kappa*1_danger <= pressure + tail + middle-leak proxy",
            "parabolic_time": "tau = nu*2^(2K)*t",
        },
        "parameters": {
            "gamma_thresholds": list(thresholds),
            "kappa_candidates": list(kappas),
            "middle_alpha_threshold": middle_alpha_threshold,
            "gap_relative_floor": gap_relative_floor,
            "candidate_remainder_coefficients": {
                "pressure": pressure_coefficient,
                "tail": tail_coefficient,
                "middle": middle_coefficient,
            },
        },
        "checkpoints": rows,
        "budget_trajectories": budget_intervals(
            points,
            thresholds,
            kappas,
            pressure_coefficient=pressure_coefficient,
            tail_coefficient=tail_coefficient,
            middle_coefficient=middle_coefficient,
        ),
        "cutoff_summary": cutoff_summary,
        "cutoff_count": len({point.cutoff for point in points}),
        "uniform_candidate_tested_across_multiple_cutoffs": len({point.cutoff for point in points}) >= 2,
        "limitations": [
            "finite saved Galerkin checkpoints only",
            "finite differences do not determine the exact material derivative",
            "packet projection introduces unresolved commutator terms",
            "pressure-Hessian rotation uses a regularized eigenvalue gap",
            "candidate remainder coefficients are discovery parameters, not theorem constants",
            "no interpolation between checkpoints",
            "no cutoff-uniform estimate, BKM theorem, or Clay promotion",
        ],
    }


def main() -> None:
    args = parse_args()
    residence_payload = json.loads(args.residence_json.read_text(encoding="utf-8"))
    result = audit(
        residence_payload,
        parse_float_list(args.gamma_thresholds),
        parse_float_list(args.kappa_candidates),
        middle_alpha_threshold=args.middle_alpha_threshold,
        gap_relative_floor=args.gap_relative_floor,
        pressure_coefficient=args.pressure_remainder_coefficient,
        tail_coefficient=args.tail_remainder_coefficient,
        middle_coefficient=args.middle_remainder_coefficient,
        allow_missing_state=args.allow_missing_state,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "checkpoint_count": len(result["checkpoints"]),
        "coherence_available_count": sum(bool(row["coherence_available"]) for row in result["checkpoints"]),
        "trajectory_count": len(result["budget_trajectories"]),
        "cutoff_count": result["cutoff_count"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
