#!/usr/bin/env python3
"""Compare replacement depletion currencies on exact Galerkin checkpoints.

The first local currency, max(-A_dot_self_advective, 0), was falsified by the
positive-transfer triad.  This audit evaluates four nonnegative replacements:

* vorticity-direction turnover;
* smooth spectral-projector tangent distance;
* cumulative cross-shell coherence activity;
* the positive lambda_2/alpha_2 branch on the simple-spectrum region.

All rates are normalized by the target-shell parabolic rate.  The audit is a
finite-Galerkin proof-search instrument only; it does not identify any candidate
with the analytic depletion term required by the continuum residence theorem.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import tempfile
from pathlib import Path
from typing import Any

import numpy as np

from ns_galerkin_coherence_core import (
    _soft_projector_and_derivative,
    curl_from_gradient,
    galerkin_packet_rhs_components,
    load_raw_state,
    spectral_gradient,
    strain_from_gradient,
)

CURRENCY_NAMES = (
    "direction_turnover",
    "spectral_projector_turnover",
    "cross_shell_coherence_activity",
    "middle_simple_spectrum_alignment",
)


def parse_floats(raw: str) -> tuple[float, ...]:
    values = tuple(sorted({float(item.strip()) for item in raw.split(",") if item.strip()}))
    if not values or any(not math.isfinite(value) or value < 0.0 for value in values):
        raise ValueError("expected a nonempty list of finite nonnegative floats")
    return values


def parse_ints(raw: str) -> tuple[int, ...]:
    values = tuple(sorted({int(item.strip()) for item in raw.split(",") if item.strip()}))
    if not values or any(value < 1 for value in values):
        raise ValueError("expected a nonempty list of positive integers")
    return values


def atomic_json(path: Path, payload: dict[str, Any], pretty: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, delete=False) as handle:
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


def direction_turnover_rate(
    omega: np.ndarray,
    omega_dot: np.ndarray,
    active_weights: np.ndarray,
    parabolic_rate: float,
) -> float:
    """Weighted RMS |D_t xi| divided by the shell parabolic rate.

    D_t xi = (I - xi xi^T) D_t omega / |omega|.  Parallel changes in vorticity
    magnitude therefore contribute exactly zero.
    """
    omega_sq = np.sum(omega * omega, axis=-1)
    omega_norm = np.sqrt(omega_sq)
    xi = np.divide(
        omega,
        omega_norm[..., None],
        out=np.zeros_like(omega),
        where=omega_norm[..., None] > 1.0e-30,
    )
    parallel = np.einsum("...i,...i->...", xi, omega_dot)
    perpendicular = omega_dot - xi * parallel[..., None]
    xi_dot = np.divide(
        perpendicular,
        omega_norm[..., None],
        out=np.zeros_like(perpendicular),
        where=omega_norm[..., None] > 1.0e-30,
    )
    squared = np.sum(xi_dot * xi_dot, axis=-1)
    return float(math.sqrt(max(float(np.sum(active_weights * squared)), 0.0)) / parabolic_rate)


def projector_turnover_rate(
    projector_dot: np.ndarray,
    active_weights: np.ndarray,
    parabolic_rate: float,
) -> float:
    """Weighted RMS Frobenius tangent speed of the smooth strain projector."""
    squared = np.sum(projector_dot * projector_dot, axis=(-2, -1))
    return float(math.sqrt(max(float(np.sum(active_weights * squared)), 0.0)) / parabolic_rate)


def currency_snapshot(
    raw_hat: np.ndarray,
    nu: float,
    target_shell: int,
    exact_budget: dict[str, Any],
    *,
    soft_beta_dimensionless: float = 8.0,
    gap_relative_floor: float = 1.0e-4,
) -> dict[str, Any]:
    rhs = galerkin_packet_rhs_components(raw_hat, nu, target_shell)
    wave = rhs["wave"]
    packet_gradient = spectral_gradient(rhs["packet_hat"], wave)
    strain = strain_from_gradient(packet_gradient)
    omega = curl_from_gradient(packet_gradient)
    omega_sq = np.sum(omega * omega, axis=-1)
    total_omega_sq = float(np.sum(omega_sq))
    if total_omega_sq <= 1.0e-30:
        raise ValueError("target packet has zero vorticity weight")
    weights = omega_sq / total_omega_sq

    eigenvalues, eigenvectors = np.linalg.eigh(strain)
    eigenvalues = eigenvalues[..., ::-1]
    eigenvectors = eigenvectors[..., :, ::-1]
    parabolic_rate = nu * float(2 ** (2 * target_shell))
    beta = soft_beta_dimensionless / parabolic_rate

    total_gradient_dot = spectral_gradient(rhs["total_rhs_hat"], wave)
    total_strain_dot = strain_from_gradient(total_gradient_dot)
    total_omega_dot = curl_from_gradient(total_gradient_dot)
    _, projector_dot = _soft_projector_and_derivative(
        eigenvalues, eigenvectors, total_strain_dot, beta
    )

    direction = direction_turnover_rate(omega, total_omega_dot, weights, parabolic_rate)
    projector = projector_turnover_rate(projector_dot, weights, parabolic_rate)

    components = exact_budget["component_derivatives"]
    cross_advective = float(
        components["cross_shell_advective"]["parabolic_normalized_alignment_derivative"]
    )
    cross_pressure = float(
        components["cross_shell_pressure"]["parabolic_normalized_alignment_derivative"]
    )
    cross_shell_activity = abs(cross_advective + cross_pressure)

    projections = np.einsum("...ji,...j->...i", eigenvectors, omega)
    alpha2 = np.divide(
        projections[..., 1] ** 2,
        omega_sq,
        out=np.zeros_like(omega_sq),
        where=omega_sq > 1.0e-30,
    )
    strain_scale = np.sqrt(np.sum(eigenvalues * eigenvalues, axis=-1))
    gap12 = eigenvalues[..., 0] - eigenvalues[..., 1]
    gap23 = eigenvalues[..., 1] - eigenvalues[..., 2]
    floor = gap_relative_floor * strain_scale + 1.0e-30
    middle_simple = (gap12 > floor) & (gap23 > floor) & (omega_sq > 1.0e-30)
    middle_density = (
        middle_simple.astype(float)
        * np.maximum(eigenvalues[..., 1], 0.0)
        * alpha2
    )
    middle_currency = float(np.sum(weights * middle_density) / parabolic_rate)
    middle_coverage = float(np.sum(weights[middle_simple]))

    return {
        "parabolic_rate": parabolic_rate,
        "currency_values": {
            "direction_turnover": direction,
            "spectral_projector_turnover": projector,
            "cross_shell_coherence_activity": cross_shell_activity,
            "middle_simple_spectrum_alignment": middle_currency,
        },
        "diagnostics": {
            "cross_shell_advective_alignment_rate": cross_advective,
            "cross_shell_pressure_alignment_rate": cross_pressure,
            "middle_simple_spectrum_enstrophy_fraction": middle_coverage,
            "middle_degenerate_region_contributes_zero": True,
            "direction_turnover_ignores_parallel_vorticity_growth": True,
            "spectral_projector_currency_is_tangent_length_not_endpoint_distance": True,
        },
        "authority": {
            "finite_galerkin_candidate_currency": True,
            "analytic_depletion_identification": False,
            "cutoff_uniform_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
    }


def _chronological_groups(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    groups: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        groups.setdefault(row["trajectory_id"], []).append(row)
    for trajectory_id, trajectory_rows in groups.items():
        trajectory_rows.sort(key=lambda item: item["time"])
        times = [item["time"] for item in trajectory_rows]
        if len(times) != len(set(times)) or any(right <= left for left, right in zip(times, times[1:])):
            raise ValueError(f"bad chronology for trajectory {trajectory_id!r}")
    return groups


def integrate_currency_rows(
    rows: list[dict[str, Any]], thresholds: tuple[float, ...]
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for trajectory_id, trajectory_rows in sorted(_chronological_groups(rows).items()):
        totals = {name: 0.0 for name in CURRENCY_NAMES}
        total_remainder = 0.0
        interval_rows: list[dict[str, Any]] = []
        dangerous_totals = {
            str(threshold): {name: 0.0 for name in CURRENCY_NAMES}
            for threshold in thresholds
        }
        dangerous_remainders = {str(threshold): 0.0 for threshold in thresholds}
        for left, right in zip(trajectory_rows, trajectory_rows[1:]):
            duration = right["time"] - left["time"]
            rate = left["parabolic_rate"]
            if not math.isclose(rate, right["parabolic_rate"], rel_tol=1.0e-12, abs_tol=1.0e-15):
                raise ValueError("parabolic-rate mismatch within trajectory")
            dtau = duration * rate
            integrated = {
                name: 0.5 * (left["currencies"][name] + right["currencies"][name]) * dtau
                for name in CURRENCY_NAMES
            }
            remainder = 0.5 * (left["positive_remainder"] + right["positive_remainder"]) * dtau
            for name, value in integrated.items():
                totals[name] += value
            total_remainder += remainder
            classifications: dict[str, str] = {}
            for threshold in thresholds:
                key = str(threshold)
                gamma_min = min(left["gamma"], right["gamma"])
                gamma_max = max(left["gamma"], right["gamma"])
                if gamma_min >= threshold:
                    classification = "certainly_dangerous"
                    for name, value in integrated.items():
                        dangerous_totals[key][name] += value
                    dangerous_remainders[key] += remainder
                elif gamma_max < threshold:
                    classification = "certainly_safe"
                else:
                    classification = "unresolved_crossing"
                classifications[key] = classification
            interval_rows.append(
                {
                    "from_checkpoint": left["checkpoint_index"],
                    "to_checkpoint": right["checkpoint_index"],
                    "physical_duration": duration,
                    "parabolic_duration": dtau,
                    "integrated_currency": integrated,
                    "integrated_positive_remainder": remainder,
                    "threshold_classifications": classifications,
                }
            )
        currency_summaries = {
            name: {
                "integrated_currency": totals[name],
                "integrated_positive_remainder": total_remainder,
                "theta_emp": total_remainder / totals[name] if totals[name] > 0.0 else None,
            }
            for name in CURRENCY_NAMES
        }
        dangerous_summaries: dict[str, Any] = {}
        for threshold in thresholds:
            key = str(threshold)
            dangerous_summaries[key] = {
                name: {
                    "integrated_currency": dangerous_totals[key][name],
                    "integrated_positive_remainder": dangerous_remainders[key],
                    "theta_emp": (
                        dangerous_remainders[key] / dangerous_totals[key][name]
                        if dangerous_totals[key][name] > 0.0
                        else None
                    ),
                }
                for name in CURRENCY_NAMES
            }
        output.append(
            {
                "trajectory_id": trajectory_id,
                "intervals": interval_rows,
                "currency_integrals": currency_summaries,
                "certainly_dangerous_integrals": dangerous_summaries,
                "cross_shell_cumulative_budget": totals["cross_shell_coherence_activity"],
            }
        )
    return output


def validate_currency_rows(
    rows: list[dict[str, Any]],
    thresholds: tuple[float, ...],
    kappas: tuple[float, ...],
    required_cutoffs: tuple[int, ...],
    holdout_trajectories: tuple[str, ...],
) -> dict[str, Any]:
    if not rows:
        raise ValueError("no currency rows")
    trajectories = sorted({row["trajectory_id"] for row in rows})
    if holdout_trajectories:
        missing = sorted(set(holdout_trajectories) - set(trajectories))
        if missing:
            raise ValueError(f"unknown holdout trajectories: {missing}")
        holdout = set(holdout_trajectories)
    elif len(trajectories) > 1:
        holdout = {trajectories[-1]}
    else:
        holdout = set()
    train = [
        row for row in rows
        if row["trajectory_id"] not in holdout and row["tight"] and row["gamma"] is not None
    ]
    test = [
        row for row in rows
        if row["trajectory_id"] in holdout and row["tight"] and row["gamma"] is not None
    ]
    if not train:
        raise ValueError("training set has no eligible currency rows")
    if holdout and not test:
        raise ValueError("holdout set has no eligible currency rows")

    audits: list[dict[str, Any]] = []
    for currency_name in CURRENCY_NAMES:
        for threshold in thresholds:
            for kappa in kappas:
                training_excursions = [row for row in train if row["gamma"] >= threshold]
                holdout_excursions = [row for row in test if row["gamma"] >= threshold]
                training_margins = [row["currencies"][currency_name] - kappa for row in training_excursions]
                holdout_margins = [row["currencies"][currency_name] - kappa for row in holdout_excursions]
                nonvacuous = bool(training_excursions) and bool(holdout_excursions)
                holdout_pass = nonvacuous and all(margin >= -1.0e-10 for margin in holdout_margins)
                audits.append(
                    {
                        "currency": currency_name,
                        "gamma_threshold": threshold,
                        "kappa": kappa,
                        "training_excursion_count": len(training_excursions),
                        "holdout_excursion_count": len(holdout_excursions),
                        "nonvacuous_excursion_test": nonvacuous,
                        "training_minimum_currency_minus_kappa": min(training_margins) if training_margins else None,
                        "holdout_minimum_currency_minus_kappa": min(holdout_margins) if holdout_margins else None,
                        "heldout_danger_expenditure_passes": holdout_pass,
                    }
                )
    observed_cutoffs = sorted({row["cutoff"] for row in rows})
    missing_cutoffs = sorted(set(required_cutoffs) - set(observed_cutoffs))
    by_currency = {
        name: any(
            audit["currency"] == name and audit["heldout_danger_expenditure_passes"]
            for audit in audits
        )
        for name in CURRENCY_NAMES
    }
    return {
        "required_cutoffs": list(required_cutoffs),
        "observed_cutoffs": observed_cutoffs,
        "missing_required_cutoffs": missing_cutoffs,
        "matched_cutoff_set_complete": not missing_cutoffs,
        "trajectory_ids": trajectories,
        "holdout_trajectories": sorted(holdout),
        "parameter_audits": audits,
        "currency_has_nonvacuous_heldout_candidate": by_currency,
        "any_candidate_currency_passes_sampled_heldout_gate": any(by_currency.values()),
        "heldout_nonvacuous_excursion_coverage": any(
            audit["nonvacuous_excursion_test"] for audit in audits
        ),
    }


def audit(
    budget_payload: dict[str, Any],
    thresholds: tuple[float, ...],
    kappas: tuple[float, ...],
    required_cutoffs: tuple[int, ...],
    holdout_trajectories: tuple[str, ...] = (),
    *,
    soft_beta_dimensionless: float = 8.0,
    gap_relative_floor: float = 1.0e-4,
) -> dict[str, Any]:
    checkpoints = budget_payload.get("checkpoints")
    if not isinstance(checkpoints, list) or not checkpoints:
        raise ValueError("budget payload has no checkpoints")
    output_checkpoints: list[dict[str, Any]] = []
    rows: list[dict[str, Any]] = []
    for position, checkpoint in enumerate(checkpoints):
        exact = checkpoint.get("exact_galerkin_alignment_budget")
        if not isinstance(exact, dict):
            raise ValueError("every checkpoint must have an exact Galerkin alignment budget")
        if "time" not in checkpoint or "source_state" not in checkpoint:
            raise ValueError("every checkpoint must carry explicit time and source_state")
        time = float(checkpoint["time"])
        raw_hat, nu, state_time = load_raw_state(Path(str(checkpoint["source_state"])))
        if state_time is not None and not math.isclose(state_time, time, abs_tol=1.0e-12):
            raise ValueError("checkpoint and NPZ physical times disagree")
        snapshot = currency_snapshot(
            raw_hat,
            nu,
            int(checkpoint["target_shell"]),
            exact,
            soft_beta_dimensionless=soft_beta_dimensionless,
            gap_relative_floor=gap_relative_floor,
        )
        enriched = dict(checkpoint)
        enriched["candidate_depletion_currency_audit"] = snapshot
        enriched["truth_authority"] = False
        enriched["theorem_authority"] = False
        enriched["promoted"] = False
        output_checkpoints.append(enriched)
        absorption = exact["candidate_absorption"]
        rows.append(
            {
                "trajectory_id": str(checkpoint.get("trajectory_id", "aggregate-trajectory")),
                "checkpoint_index": int(checkpoint.get("checkpoint_index", position)),
                "time": time,
                "cutoff": int(exact["cutoff"]),
                "gamma": float(checkpoint["gamma"]) if checkpoint.get("gamma") is not None else None,
                "tight": bool(checkpoint.get("packet_tight", False)),
                "parabolic_rate": float(snapshot["parabolic_rate"]),
                "currencies": dict(snapshot["currency_values"]),
                "positive_remainder": float(absorption["total_positive_remainder"]),
            }
        )
    _chronological_groups(rows)
    validation = validate_currency_rows(
        rows, thresholds, kappas, required_cutoffs, holdout_trajectories
    )
    integrals = integrate_currency_rows(rows, thresholds)
    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_candidate_comparison": True,
            "analytic_depletion_identification": False,
            "cutoff_uniform_authority": False,
            "truth_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "currency_names": list(CURRENCY_NAMES),
        "definitions": {
            "direction_turnover": "weighted RMS |(I-xi xi^T) omega_dot/|omega|| divided by nu 2^(2K)",
            "spectral_projector_turnover": "weighted RMS Frobenius speed of P_beta(S) divided by nu 2^(2K)",
            "cross_shell_coherence_activity": "absolute cross-shell advective plus pressure contribution to parabolic A_dot",
            "middle_simple_spectrum_alignment": "weighted positive lambda2 alpha2 divided by nu 2^(2K), zeroed on unresolved eigenspace collisions",
        },
        "checkpoints": output_checkpoints,
        "trajectory_integrals": integrals,
        "heldout_validation": validation,
        "limitations": [
            "a sampled candidate margin is not a proof that danger forces analytic depletion",
            "projector turnover is an infinitesimal path-length rate, not endpoint geodesic distance",
            "the middle branch is deliberately zero on degenerate regions",
            "cross-shell activity is unsigned variation and is not automatically dissipative",
            "cutoff agreement on N32/N48/N64 is not a compactness theorem",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--budget-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--gamma-thresholds", default="0.5,0.9,1.0")
    parser.add_argument("--kappa-candidates", default="0.01,0.05,0.1,0.25")
    parser.add_argument("--required-cutoffs", default="32,48,64")
    parser.add_argument("--holdout-trajectory", action="append", default=[])
    parser.add_argument("--soft-projector-beta", type=float, default=8.0)
    parser.add_argument("--gap-relative-floor", type=float, default=1.0e-4)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    result = audit(
        json.loads(args.budget_json.read_text(encoding="utf-8")),
        parse_floats(args.gamma_thresholds),
        parse_floats(args.kappa_candidates),
        parse_ints(args.required_cutoffs),
        tuple(args.holdout_trajectory),
        soft_beta_dimensionless=args.soft_projector_beta,
        gap_relative_floor=args.gap_relative_floor,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "matched_cutoff_set_complete": result["heldout_validation"]["matched_cutoff_set_complete"],
        "any_candidate_currency_passes_sampled_heldout_gate": result["heldout_validation"]["any_candidate_currency_passes_sampled_heldout_gate"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
