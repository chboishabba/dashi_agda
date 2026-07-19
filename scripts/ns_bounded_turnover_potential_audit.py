#!/usr/bin/env python3
"""Test whether geometric turnover is productive for a bounded alignment potential.

The previous currency audit found large vorticity-direction and smooth-projector
path-length rates on a matched dangerous triad.  Path length alone is not a
finite budget: a direction or projector may rotate indefinitely.  This audit
therefore derives the exact finite-Galerkin decomposition of the bounded soft
alignment potential

    A_K = < omega_K^T P_beta(S_K) omega_K > / < |omega_K|^2 >,

into

    A_dot = direction_motion + projector_motion + weight_redistribution.

For each term it records signed escape, replenishment, and its efficiency
relative to the corresponding unsigned path-length rate.  Chronological
intervals additionally verify the one-sided bounded-potential accounting

    integral D <= A(t0) + integral G + quadrature allowance,

where D=max(-A_dot,0), G=max(A_dot,0).  This is an empirical finite-checkpoint
accounting identity, not a continuum residence theorem.
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

from ns_depletion_currency_audit import (
    direction_turnover_rate,
    parse_floats,
    parse_ints,
    projector_turnover_rate,
)
from ns_galerkin_coherence_core import (
    _soft_projector_and_derivative,
    curl_from_gradient,
    galerkin_packet_rhs_components,
    load_raw_state,
    spectral_gradient,
    strain_from_gradient,
)

POTENTIAL_CURRENCIES = (
    "net_alignment_escape",
    "direction_alignment_escape",
    "projector_alignment_escape",
    "mechanism_escape_sum",
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


def alignment_potential_derivative(
    omega: np.ndarray,
    omega_dot: np.ndarray,
    projector: np.ndarray,
    projector_dot: np.ndarray,
) -> dict[str, float]:
    """Exact quotient decomposition for A=<w a>/<w> at one tangent vector."""
    omega_sq = np.sum(omega * omega, axis=-1)
    enstrophy = float(np.mean(omega_sq))
    if enstrophy <= 1.0e-30:
        raise ValueError("zero enstrophy in alignment potential")
    omega_norm = np.sqrt(omega_sq)
    xi = np.divide(
        omega,
        omega_norm[..., None],
        out=np.zeros_like(omega),
        where=omega_norm[..., None] > 1.0e-30,
    )
    pxi = np.einsum("...ij,...j->...i", projector, xi)
    local_alignment = np.einsum("...i,...i->...", xi, pxi)
    potential = float(np.mean(omega_sq * local_alignment) / enstrophy)

    parallel = np.einsum("...i,...i->...", xi, omega_dot)
    perpendicular = omega_dot - xi * parallel[..., None]
    xi_dot = np.divide(
        perpendicular,
        omega_norm[..., None],
        out=np.zeros_like(perpendicular),
        where=omega_norm[..., None] > 1.0e-30,
    )
    direction_density = 2.0 * np.einsum("...i,...i->...", xi_dot, pxi)
    projector_density = np.einsum(
        "...i,...ij,...j->...", xi, projector_dot, xi
    )
    weight_dot = 2.0 * np.einsum("...i,...i->...", omega, omega_dot)

    direction = float(np.mean(omega_sq * direction_density) / enstrophy)
    projector_motion = float(np.mean(omega_sq * projector_density) / enstrophy)
    redistribution = float(
        np.mean(weight_dot * (local_alignment - potential)) / enstrophy
    )

    pomega = np.einsum("...ij,...j->...i", projector, omega)
    numerator = float(np.mean(np.einsum("...i,...i->...", omega, pomega)))
    enstrophy_dot = float(
        2.0 * np.mean(np.einsum("...i,...i->...", omega, omega_dot))
    )
    numerator_dot = float(
        np.mean(
            2.0 * np.einsum("...i,...i->...", omega_dot, pomega)
            + np.einsum("...i,...ij,...j->...", omega, projector_dot, omega)
        )
    )
    quotient = (numerator_dot * enstrophy - numerator * enstrophy_dot) / (
        enstrophy * enstrophy
    )
    decomposed = direction + projector_motion + redistribution
    return {
        "potential": potential,
        "direction_motion": direction,
        "projector_motion": projector_motion,
        "weight_redistribution": redistribution,
        "decomposed_derivative": decomposed,
        "quotient_derivative": quotient,
        "decomposition_residual": abs(decomposed - quotient),
        "potential_lower_bound_residual": max(-potential, 0.0),
        "potential_upper_bound_residual": max(potential - 1.0, 0.0),
    }


def bounded_potential_snapshot(
    raw_hat: np.ndarray,
    nu: float,
    target_shell: int,
    *,
    soft_beta_dimensionless: float = 8.0,
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
    parabolic_rate = nu * float(2 ** (2 * target_shell))
    beta = soft_beta_dimensionless / parabolic_rate
    projector, _ = _soft_projector_and_derivative(
        eigenvalues, eigenvectors, np.zeros_like(strain), beta
    )

    component_rows: dict[str, dict[str, float]] = {}
    sums = {
        "direction_motion": 0.0,
        "projector_motion": 0.0,
        "weight_redistribution": 0.0,
        "decomposed_derivative": 0.0,
    }
    for name, component_hat in rhs["components"].items():
        gradient_dot = spectral_gradient(component_hat, wave)
        strain_dot = strain_from_gradient(gradient_dot)
        omega_dot = curl_from_gradient(gradient_dot)
        _, projector_dot = _soft_projector_and_derivative(
            eigenvalues, eigenvectors, strain_dot, beta
        )
        row = alignment_potential_derivative(
            omega, omega_dot, projector, projector_dot
        )
        component_rows[name] = {
            key: value / parabolic_rate
            for key, value in row.items()
            if key not in {
                "potential",
                "potential_lower_bound_residual",
                "potential_upper_bound_residual",
            }
        }
        for key in sums:
            sums[key] += row[key]

    total_gradient_dot = spectral_gradient(rhs["total_rhs_hat"], wave)
    total_strain_dot = strain_from_gradient(total_gradient_dot)
    total_omega_dot = curl_from_gradient(total_gradient_dot)
    _, total_projector_dot = _soft_projector_and_derivative(
        eigenvalues, eigenvectors, total_strain_dot, beta
    )
    direct = alignment_potential_derivative(
        omega, total_omega_dot, projector, total_projector_dot
    )
    direct_parabolic = {
        key: value / parabolic_rate
        for key, value in direct.items()
        if key not in {
            "potential",
            "potential_lower_bound_residual",
            "potential_upper_bound_residual",
        }
    }
    direction_path = direction_turnover_rate(
        omega, total_omega_dot, weights, parabolic_rate
    )
    projector_path = projector_turnover_rate(
        total_projector_dot, weights, parabolic_rate
    )
    total_dot = direct_parabolic["quotient_derivative"]
    direction_signed = direct_parabolic["direction_motion"]
    projector_signed = direct_parabolic["projector_motion"]
    redistribution_signed = direct_parabolic["weight_redistribution"]
    net_escape = max(-total_dot, 0.0)
    replenishment = max(total_dot, 0.0)
    direction_escape = max(-direction_signed, 0.0)
    projector_escape = max(-projector_signed, 0.0)
    redistribution_escape = max(-redistribution_signed, 0.0)
    mechanism_escape_sum = direction_escape + projector_escape + redistribution_escape

    return {
        "parabolic_rate": parabolic_rate,
        "soft_projector_beta_dimensionless": soft_beta_dimensionless,
        "soft_alignment_potential": direct["potential"],
        "component_signed_derivatives": component_rows,
        "direct_signed_derivative": direct_parabolic,
        "component_sum_residuals": {
            key: abs(sums[key] / parabolic_rate - direct_parabolic[key])
            for key in sums
        },
        "path_length_rates": {
            "direction_turnover": direction_path,
            "spectral_projector_turnover": projector_path,
        },
        "one_sided_rates": {
            "net_alignment_escape": net_escape,
            "alignment_replenishment": replenishment,
            "direction_alignment_escape": direction_escape,
            "projector_alignment_escape": projector_escape,
            "redistribution_alignment_escape": redistribution_escape,
            "mechanism_escape_sum": mechanism_escape_sum,
        },
        "productive_turnover_efficiency": {
            "direction_escape_over_path_length": (
                direction_escape / direction_path if direction_path > 0.0 else None
            ),
            "projector_escape_over_path_length": (
                projector_escape / projector_path if projector_path > 0.0 else None
            ),
        },
        "authority": {
            "exact_finite_galerkin_tangent_identity": True,
            "bounded_potential_accounting_candidate": True,
            "danger_forces_signed_escape": False,
            "continuum_budget_authority": False,
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
    for trajectory_id, trajectory in groups.items():
        trajectory.sort(key=lambda row: row["time"])
        times = [row["time"] for row in trajectory]
        if len(times) != len(set(times)) or any(
            right <= left for left, right in zip(times, times[1:])
        ):
            raise ValueError(f"bad chronology for trajectory {trajectory_id!r}")
    return groups


def integrate_bounded_potential_rows(
    rows: list[dict[str, Any]], thresholds: tuple[float, ...]
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for trajectory_id, trajectory in sorted(_chronological_groups(rows).items()):
        intervals: list[dict[str, Any]] = []
        total_depletion = 0.0
        total_replenishment = 0.0
        total_quadrature_allowance = 0.0
        certainly_dangerous_time = {str(threshold): 0.0 for threshold in thresholds}
        for left, right in zip(trajectory, trajectory[1:]):
            if not math.isclose(
                left["parabolic_rate"], right["parabolic_rate"],
                rel_tol=1.0e-12, abs_tol=1.0e-15,
            ):
                raise ValueError("parabolic-rate mismatch within trajectory")
            dt = right["time"] - left["time"]
            dtau = dt * left["parabolic_rate"]
            integrated_depletion = 0.5 * (
                left["depletion"] + right["depletion"]
            ) * dtau
            integrated_replenishment = 0.5 * (
                left["replenishment"] + right["replenishment"]
            ) * dtau
            integrated_derivative = 0.5 * (
                left["potential_derivative"] + right["potential_derivative"]
            ) * dtau
            observed_delta = right["potential"] - left["potential"]
            quadrature_residual = observed_delta - integrated_derivative
            balance_residual = integrated_depletion - (
                left["potential"] + integrated_replenishment - right["potential"]
            )
            classifications: dict[str, str] = {}
            gamma_min = min(left["gamma"], right["gamma"])
            gamma_max = max(left["gamma"], right["gamma"])
            for threshold in thresholds:
                key = str(threshold)
                if gamma_min >= threshold:
                    classifications[key] = "certainly_dangerous"
                    certainly_dangerous_time[key] += dtau
                elif gamma_max < threshold:
                    classifications[key] = "certainly_safe"
                else:
                    classifications[key] = "unresolved_crossing"
            total_depletion += integrated_depletion
            total_replenishment += integrated_replenishment
            total_quadrature_allowance += abs(quadrature_residual)
            intervals.append({
                "from_checkpoint": left["checkpoint_index"],
                "to_checkpoint": right["checkpoint_index"],
                "physical_duration": dt,
                "parabolic_duration": dtau,
                "potential_start": left["potential"],
                "potential_end": right["potential"],
                "observed_potential_delta": observed_delta,
                "trapezoid_integrated_potential_derivative": integrated_derivative,
                "derivative_quadrature_residual": quadrature_residual,
                "integrated_depletion": integrated_depletion,
                "integrated_replenishment": integrated_replenishment,
                "one_sided_balance_residual": balance_residual,
                "threshold_classifications": classifications,
            })
        initial = trajectory[0]["potential"]
        final = trajectory[-1]["potential"]
        upper = initial + total_replenishment + total_quadrature_allowance
        output.append({
            "trajectory_id": trajectory_id,
            "intervals": intervals,
            "initial_potential": initial,
            "final_potential": final,
            "integrated_depletion": total_depletion,
            "integrated_replenishment": total_replenishment,
            "quadrature_allowance": total_quadrature_allowance,
            "bounded_potential_upper": upper,
            "bounded_potential_margin": upper - total_depletion,
            "bounded_potential_budget_holds_with_quadrature_allowance": (
                total_depletion <= upper + 1.0e-10
            ),
            "certainly_dangerous_parabolic_residence": certainly_dangerous_time,
        })
    return output


def validate_signed_escape(
    rows: list[dict[str, Any]],
    thresholds: tuple[float, ...],
    kappas: tuple[float, ...],
    required_cutoffs: tuple[int, ...],
    holdout_trajectories: tuple[str, ...],
) -> dict[str, Any]:
    trajectories = sorted({row["trajectory_id"] for row in rows})
    holdout = set(holdout_trajectories)
    if holdout:
        missing = sorted(holdout - set(trajectories))
        if missing:
            raise ValueError(f"unknown holdout trajectories: {missing}")
    elif len(trajectories) > 1:
        holdout = {trajectories[-1]}
    train = [
        row for row in rows
        if row["trajectory_id"] not in holdout and row["tight"] and row["gamma"] is not None
    ]
    test = [
        row for row in rows
        if row["trajectory_id"] in holdout and row["tight"] and row["gamma"] is not None
    ]
    if not train or (holdout and not test):
        raise ValueError("training or holdout signed-potential rows are empty")
    audits: list[dict[str, Any]] = []
    for currency in POTENTIAL_CURRENCIES:
        for threshold in thresholds:
            for kappa in kappas:
                train_exc = [row for row in train if row["gamma"] >= threshold]
                test_exc = [row for row in test if row["gamma"] >= threshold]
                train_margins = [row["currencies"][currency] - kappa for row in train_exc]
                test_margins = [row["currencies"][currency] - kappa for row in test_exc]
                nonvacuous = bool(train_exc) and bool(test_exc)
                audits.append({
                    "currency": currency,
                    "gamma_threshold": threshold,
                    "kappa": kappa,
                    "training_excursion_count": len(train_exc),
                    "holdout_excursion_count": len(test_exc),
                    "nonvacuous_excursion_test": nonvacuous,
                    "training_minimum_currency_minus_kappa": (
                        min(train_margins) if train_margins else None
                    ),
                    "holdout_minimum_currency_minus_kappa": (
                        min(test_margins) if test_margins else None
                    ),
                    "heldout_danger_forces_signed_escape": (
                        nonvacuous and all(margin >= -1.0e-10 for margin in test_margins)
                    ),
                })
    observed = sorted({row["cutoff"] for row in rows})
    missing_cutoffs = sorted(set(required_cutoffs) - set(observed))
    by_currency = {
        currency: any(
            audit["currency"] == currency
            and audit["heldout_danger_forces_signed_escape"]
            for audit in audits
        )
        for currency in POTENTIAL_CURRENCIES
    }
    return {
        "required_cutoffs": list(required_cutoffs),
        "observed_cutoffs": observed,
        "missing_required_cutoffs": missing_cutoffs,
        "matched_cutoff_set_complete": not missing_cutoffs,
        "holdout_trajectories": sorted(holdout),
        "parameter_audits": audits,
        "currency_has_nonvacuous_heldout_signed_escape": by_currency,
        "any_signed_escape_currency_passes_heldout": any(by_currency.values()),
    }


def audit(
    depletion_payload: dict[str, Any],
    thresholds: tuple[float, ...],
    kappas: tuple[float, ...],
    required_cutoffs: tuple[int, ...],
    holdout_trajectories: tuple[str, ...] = (),
    *,
    soft_beta_dimensionless: float = 8.0,
) -> dict[str, Any]:
    checkpoints = depletion_payload.get("checkpoints")
    if not isinstance(checkpoints, list) or not checkpoints:
        raise ValueError("depletion payload has no checkpoints")
    enriched: list[dict[str, Any]] = []
    rows: list[dict[str, Any]] = []
    for position, checkpoint in enumerate(checkpoints):
        if "time" not in checkpoint or "source_state" not in checkpoint:
            raise ValueError("every checkpoint must carry time and source_state")
        time = float(checkpoint["time"])
        raw_hat, nu, state_time = load_raw_state(Path(str(checkpoint["source_state"])))
        if state_time is not None and not math.isclose(state_time, time, abs_tol=1.0e-12):
            raise ValueError("checkpoint and NPZ times disagree")
        snapshot = bounded_potential_snapshot(
            raw_hat,
            nu,
            int(checkpoint["target_shell"]),
            soft_beta_dimensionless=soft_beta_dimensionless,
        )
        row = dict(checkpoint)
        row["bounded_turnover_potential_audit"] = snapshot
        row["truth_authority"] = False
        row["theorem_authority"] = False
        row["promoted"] = False
        enriched.append(row)
        one_sided = snapshot["one_sided_rates"]
        direct = snapshot["direct_signed_derivative"]
        rows.append({
            "trajectory_id": str(checkpoint.get("trajectory_id", "aggregate-trajectory")),
            "checkpoint_index": int(checkpoint.get("checkpoint_index", position)),
            "time": time,
            "cutoff": int(checkpoint.get("cutoff", raw_hat.shape[0])),
            "gamma": float(checkpoint["gamma"]) if checkpoint.get("gamma") is not None else None,
            "tight": bool(checkpoint.get("packet_tight", False)),
            "parabolic_rate": float(snapshot["parabolic_rate"]),
            "potential": float(snapshot["soft_alignment_potential"]),
            "potential_derivative": float(direct["quotient_derivative"]),
            "depletion": float(one_sided["net_alignment_escape"]),
            "replenishment": float(one_sided["alignment_replenishment"]),
            "currencies": {
                currency: float(one_sided[currency]) for currency in POTENTIAL_CURRENCIES
            },
        })
    _chronological_groups(rows)
    return {
        "schema_version": "1.0.0",
        "authority": {
            "exact_finite_galerkin_potential_decomposition": True,
            "bounded_one_sided_accounting_checked": True,
            "danger_forces_signed_escape": False,
            "cutoff_uniform_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "potential": "A_K=<omega^T P_beta(S) omega>/<|omega|^2>, in [0,1]",
            "direction_motion": "weighted signed 2 xi_dot.P_beta xi",
            "projector_motion": "weighted signed xi.P_beta_dot xi",
            "weight_redistribution": "weighted w_dot(a-A)/E",
            "depletion": "max(-A_dot,0)",
            "replenishment": "max(A_dot,0)",
            "bounded_budget": "integral depletion <= A(t0)+integral replenishment+quadrature allowance",
        },
        "checkpoints": enriched,
        "trajectory_bounded_budgets": integrate_bounded_potential_rows(rows, thresholds),
        "heldout_signed_escape_validation": validate_signed_escape(
            rows, thresholds, kappas, required_cutoffs, holdout_trajectories
        ),
        "limitations": [
            "large unsigned turnover need not produce signed escape from the bounded potential",
            "checkpoint trapezoids require an explicit quadrature allowance",
            "replenishment still requires pressure/commutator/viscous control",
            "one matched triad family is not a cutoff-uniform theorem",
            "no BKM, global-regularity, or Clay promotion",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depletion-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--gamma-thresholds", default="0.5,0.9,1.0")
    parser.add_argument("--kappa-candidates", default="0.01,0.05,0.1,0.25")
    parser.add_argument("--required-cutoffs", default="32,48,64")
    parser.add_argument("--holdout-trajectory", action="append", default=[])
    parser.add_argument("--soft-projector-beta", type=float, default=8.0)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    result = audit(
        json.loads(args.depletion_json.read_text(encoding="utf-8")),
        parse_floats(args.gamma_thresholds),
        parse_floats(args.kappa_candidates),
        parse_ints(args.required_cutoffs),
        tuple(args.holdout_trajectory),
        soft_beta_dimensionless=args.soft_projector_beta,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "matched_cutoff_set_complete": result["heldout_signed_escape_validation"]["matched_cutoff_set_complete"],
        "any_signed_escape_currency_passes_heldout": result["heldout_signed_escape_validation"]["any_signed_escape_currency_passes_heldout"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
