#!/usr/bin/env python3
"""Audit a bounded transfer-phase potential with exact Galerkin derivatives.

The top-strain alignment potential was falsified on the matched dangerous triad:
large geometric turnover did not produce signed escape.  This lane instead uses
an observable tied directly to the dangerous-transfer ratio,

    B_K = Q_{K,+} / (Q_{K,+} + 2 nu D_K)
        = Gamma_K / (1 + Gamma_K).

Here Q_K is the signed target-packet nonlinear transfer and D_K is packet
dissipation.  On the strict positive-transfer region the script computes exact
finite-Galerkin tangent derivatives of Q_K, D_K, Gamma_K, and B_K, including a
linear decomposition by target/off-packet nonlinear and viscous state tangents.
At the positive-part kink Q_K=0 it fails closed rather than inventing a
classical derivative.
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

from ns_bounded_turnover_potential_audit import integrate_bounded_potential_rows
from ns_depletion_currency_audit import parse_floats, parse_ints
from ns_galerkin_coherence_core import (
    frequency_grid,
    leray_project_hat,
    load_raw_state,
    nonlinear_momentum_components,
    packet_mask,
    spectral_gradient,
)

COMPACT_CURRENCIES = (
    "net_compact_gamma_escape",
    "target_nonlinear_escape",
    "off_packet_nonlinear_escape",
    "viscous_escape",
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


def nonlinear_tangent_hat(
    state_hat: np.ndarray,
    tangent_hat: np.ndarray,
    wave: np.ndarray,
    norm_sq: np.ndarray,
    dealias: np.ndarray,
) -> np.ndarray:
    """Derivative of -P[(u.grad)u] in the tangent direction v."""
    state = np.fft.ifftn(state_hat, axes=(0, 1, 2)).real
    tangent = np.fft.ifftn(tangent_hat, axes=(0, 1, 2)).real
    state_gradient = spectral_gradient(state_hat, wave)
    tangent_gradient = spectral_gradient(tangent_hat, wave)
    convection_tangent = (
        np.einsum("...j,...ij->...i", tangent, state_gradient)
        + np.einsum("...j,...ij->...i", state, tangent_gradient)
    )
    convection_hat = np.fft.fftn(convection_tangent, axes=(0, 1, 2))
    advective = -convection_hat
    dot = np.einsum("...i,...i->...", wave, convection_hat)
    pressure = np.zeros_like(convection_hat)
    nonzero = norm_sq > 0.0
    pressure[nonzero] = wave[nonzero] * (
        dot[nonzero] / norm_sq[nonzero]
    )[:, None]
    return (advective + pressure) * dealias[..., None]


def _state_geometry(raw_hat: np.ndarray, nu: float, target_shell: int) -> dict[str, Any]:
    if raw_hat.ndim != 4 or raw_hat.shape[-1] != 3 or len(set(raw_hat.shape[:3])) != 1:
        raise ValueError("expected raw_hat shape (N,N,N,3)")
    if not math.isfinite(nu) or nu <= 0.0:
        raise ValueError("viscosity must be finite and positive")
    n = int(raw_hat.shape[0])
    wave, norm_sq, norm, dealias = frequency_grid(n)
    retained = leray_project_hat(raw_hat * dealias[..., None], wave, norm_sq)
    packet = packet_mask(norm, target_shell, dealias)
    packet_hat = retained * packet[..., None]
    advective, pressure = nonlinear_momentum_components(
        retained, wave, norm_sq, dealias
    )
    nonlinear = advective + pressure
    nonlinear_packet = nonlinear * packet[..., None]
    viscous = -nu * norm_sq[..., None] * retained
    total_rhs = nonlinear + viscous
    packet_selector = packet[..., None]
    components = {
        "target_advective": advective * packet_selector,
        "target_pressure": pressure * packet_selector,
        "off_packet_advective": advective * (~packet)[..., None],
        "off_packet_pressure": pressure * (~packet)[..., None],
        "target_viscous": viscous * packet_selector,
        "off_packet_viscous": viscous * (~packet)[..., None],
    }
    component_sum = sum(components.values(), np.zeros_like(retained))
    return {
        "cutoff": n,
        "wave": wave,
        "norm_sq": norm_sq,
        "dealias": dealias,
        "packet": packet,
        "retained_hat": retained,
        "packet_hat": packet_hat,
        "nonlinear_packet_hat": nonlinear_packet,
        "total_rhs_hat": total_rhs,
        "components": components,
        "component_sum_max_residual": float(np.max(np.abs(component_sum - total_rhs))),
    }


def compact_state_values(
    raw_hat: np.ndarray,
    nu: float,
    target_shell: int,
    *,
    positive_part_relative_floor: float = 1.0e-10,
) -> dict[str, Any]:
    geometry = _state_geometry(raw_hat, nu, target_shell)
    n = geometry["cutoff"]
    scale = float(n ** 3)
    packet = geometry["packet"]
    packet_field = geometry["packet_hat"] / scale
    nonlinear_field = geometry["nonlinear_packet_hat"] / scale
    norm_sq = geometry["norm_sq"]
    transfer = float(
        2.0 * float(2 ** target_shell)
        * np.real(np.sum(np.conjugate(packet_field[packet]) * nonlinear_field[packet]))
    )
    modal_energy = np.sum(np.abs(packet_field) ** 2, axis=-1)
    dissipation = float(np.sum(norm_sq[packet] * modal_energy[packet]))
    viscous_scale = 2.0 * nu * dissipation
    if viscous_scale <= 1.0e-30:
        raise ValueError("target packet has zero viscous denominator")
    floor = positive_part_relative_floor * (abs(transfer) + viscous_scale) + 1.0e-30
    if transfer > floor:
        branch = "strict_positive_transfer"
        transfer_positive = transfer
        gamma = transfer / viscous_scale
        compact = transfer / (transfer + viscous_scale)
    elif transfer < -floor:
        branch = "strict_negative_transfer"
        transfer_positive = 0.0
        gamma = 0.0
        compact = 0.0
    else:
        branch = "positive_part_kink_unresolved"
        transfer_positive = max(transfer, 0.0)
        gamma = transfer_positive / viscous_scale
        compact = transfer_positive / (transfer_positive + viscous_scale)
    return {
        "geometry": geometry,
        "signed_transfer_Q": transfer,
        "positive_transfer_Q_plus": transfer_positive,
        "packet_dissipation_D": dissipation,
        "viscous_denominator_2nuD": viscous_scale,
        "gamma": gamma,
        "compact_gamma_potential_B": compact,
        "positive_part_branch": branch,
        "positive_part_floor": floor,
        "compact_relation_residual": abs(
            compact - gamma / (1.0 + gamma)
        ),
    }


def _directional_derivative(
    values: dict[str, Any],
    tangent_hat: np.ndarray,
    nu: float,
    target_shell: int,
) -> dict[str, float | None]:
    geometry = values["geometry"]
    packet = geometry["packet"]
    scale = float(geometry["cutoff"] ** 3)
    packet_field = geometry["packet_hat"] / scale
    nonlinear_field = geometry["nonlinear_packet_hat"] / scale
    tangent_packet = tangent_hat * packet[..., None]
    nonlinear_dot = nonlinear_tangent_hat(
        geometry["retained_hat"],
        tangent_hat,
        geometry["wave"],
        geometry["norm_sq"],
        geometry["dealias"],
    ) * packet[..., None]
    tangent_packet_field = tangent_packet / scale
    nonlinear_dot_field = nonlinear_dot / scale
    transfer_dot = float(
        2.0 * float(2 ** target_shell)
        * np.real(
            np.sum(
                np.conjugate(tangent_packet_field[packet]) * nonlinear_field[packet]
                + np.conjugate(packet_field[packet]) * nonlinear_dot_field[packet]
            )
        )
    )
    dissipation_dot = float(
        2.0
        * np.real(
            np.sum(
                geometry["norm_sq"][packet, None]
                * np.conjugate(packet_field[packet])
                * tangent_packet_field[packet]
            )
        )
    )
    viscous_dot = 2.0 * nu * dissipation_dot
    transfer = float(values["signed_transfer_Q"])
    viscous = float(values["viscous_denominator_2nuD"])
    branch = values["positive_part_branch"]
    if branch == "strict_positive_transfer":
        gamma_dot = (transfer_dot * viscous - transfer * viscous_dot) / (
            viscous * viscous
        )
        compact_dot = (transfer_dot * viscous - transfer * viscous_dot) / (
            (transfer + viscous) ** 2
        )
    elif branch == "strict_negative_transfer":
        gamma_dot = 0.0
        compact_dot = 0.0
    else:
        gamma_dot = None
        compact_dot = None
    return {
        "signed_transfer_derivative": transfer_dot,
        "packet_dissipation_derivative": dissipation_dot,
        "viscous_denominator_derivative": viscous_dot,
        "gamma_derivative": gamma_dot,
        "compact_gamma_potential_derivative": compact_dot,
    }


def compact_gamma_snapshot(
    raw_hat: np.ndarray,
    nu: float,
    target_shell: int,
    *,
    positive_part_relative_floor: float = 1.0e-10,
    finite_difference_relative_step: float = 1.0e-7,
) -> dict[str, Any]:
    values = compact_state_values(
        raw_hat,
        nu,
        target_shell,
        positive_part_relative_floor=positive_part_relative_floor,
    )
    geometry = values["geometry"]
    direct = _directional_derivative(
        values, geometry["total_rhs_hat"], nu, target_shell
    )
    component_rows = {
        name: _directional_derivative(values, tangent, nu, target_shell)
        for name, tangent in geometry["components"].items()
    }
    derivative_keys = (
        "signed_transfer_derivative",
        "packet_dissipation_derivative",
        "viscous_denominator_derivative",
        "gamma_derivative",
        "compact_gamma_potential_derivative",
    )
    component_residuals: dict[str, float | None] = {}
    for key in derivative_keys:
        if direct[key] is None or any(row[key] is None for row in component_rows.values()):
            component_residuals[key] = None
        else:
            component_residuals[key] = abs(
                float(direct[key])
                - sum(float(row[key]) for row in component_rows.values())
            )

    parabolic_rate = nu * float(2 ** (2 * target_shell))
    compact_dot = direct["compact_gamma_potential_derivative"]
    if compact_dot is None:
        compact_dot_parabolic = None
        net_escape = None
        replenishment = None
    else:
        compact_dot_parabolic = float(compact_dot) / parabolic_rate
        net_escape = max(-compact_dot_parabolic, 0.0)
        replenishment = max(compact_dot_parabolic, 0.0)

    def component_compact(name: str) -> float | None:
        value = component_rows[name]["compact_gamma_potential_derivative"]
        return None if value is None else float(value) / parabolic_rate

    grouped = {
        "target_nonlinear": sum(
            component_compact(name) or 0.0
            for name in ("target_advective", "target_pressure")
        ),
        "off_packet_nonlinear": sum(
            component_compact(name) or 0.0
            for name in ("off_packet_advective", "off_packet_pressure")
        ),
        "viscous": sum(
            component_compact(name) or 0.0
            for name in ("target_viscous", "off_packet_viscous")
        ),
    }
    if compact_dot is None:
        currencies = {name: None for name in COMPACT_CURRENCIES}
    else:
        currencies = {
            "net_compact_gamma_escape": float(net_escape),
            "target_nonlinear_escape": max(-grouped["target_nonlinear"], 0.0),
            "off_packet_nonlinear_escape": max(-grouped["off_packet_nonlinear"], 0.0),
            "viscous_escape": max(-grouped["viscous"], 0.0),
            "mechanism_escape_sum": sum(max(-value, 0.0) for value in grouped.values()),
        }

    raw_norm = float(np.linalg.norm(geometry["retained_hat"]))
    rhs_norm = float(np.linalg.norm(geometry["total_rhs_hat"]))
    relative_rate = rhs_norm / max(raw_norm, 1.0e-30)
    epsilon = min(
        1.0e-5,
        finite_difference_relative_step / max(relative_rate, 1.0e-12),
    )
    plus = compact_state_values(
        raw_hat + epsilon * geometry["total_rhs_hat"],
        nu,
        target_shell,
        positive_part_relative_floor=positive_part_relative_floor,
    )
    minus = compact_state_values(
        raw_hat - epsilon * geometry["total_rhs_hat"],
        nu,
        target_shell,
        positive_part_relative_floor=positive_part_relative_floor,
    )
    if (
        direct["compact_gamma_potential_derivative"] is not None
        and plus["positive_part_branch"] == values["positive_part_branch"]
        and minus["positive_part_branch"] == values["positive_part_branch"]
    ):
        finite_difference = (
            plus["compact_gamma_potential_B"] - minus["compact_gamma_potential_B"]
        ) / (2.0 * epsilon)
        finite_difference_residual = abs(
            finite_difference - float(direct["compact_gamma_potential_derivative"])
        )
    else:
        finite_difference = None
        finite_difference_residual = None

    public_values = {key: value for key, value in values.items() if key != "geometry"}
    return {
        **public_values,
        "parabolic_rate": parabolic_rate,
        "direct_derivatives": direct,
        "component_derivatives": component_rows,
        "component_sum_residuals": component_residuals,
        "grouped_compact_derivatives_parabolic": grouped,
        "compact_derivative_parabolic": compact_dot_parabolic,
        "one_sided_rates": {
            "depletion": net_escape,
            "replenishment": replenishment,
        },
        "candidate_signed_escape_currencies": currencies,
        "finite_difference_check": {
            "epsilon": epsilon,
            "central_difference": finite_difference,
            "residual": finite_difference_residual,
        },
        "state_rhs_component_sum_max_residual": geometry["component_sum_max_residual"],
        "authority": {
            "exact_finite_galerkin_derivative_on_resolved_branch": True,
            "positive_part_kink_failed_closed": True,
            "danger_forces_compact_escape": False,
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
    for trajectory_id, trajectory in groups.items():
        trajectory.sort(key=lambda row: row["time"])
        times = [row["time"] for row in trajectory]
        if len(times) != len(set(times)) or any(
            right <= left for left, right in zip(times, times[1:])
        ):
            raise ValueError(f"bad chronology for trajectory {trajectory_id!r}")
    return groups


def validate_compact_escape(
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
    eligible = [
        row for row in rows
        if row["tight"] and row["gamma"] is not None and row["branch_resolved"]
    ]
    train = [row for row in eligible if row["trajectory_id"] not in holdout]
    test = [row for row in eligible if row["trajectory_id"] in holdout]
    if not train or (holdout and not test):
        raise ValueError("training or holdout compact-potential rows are empty")
    audits: list[dict[str, Any]] = []
    for currency in COMPACT_CURRENCIES:
        for threshold in thresholds:
            compact_threshold = threshold / (1.0 + threshold)
            for kappa in kappas:
                train_exc = [row for row in train if row["gamma"] >= threshold]
                test_exc = [row for row in test if row["gamma"] >= threshold]
                train_margins = [row["currencies"][currency] - kappa for row in train_exc]
                test_margins = [row["currencies"][currency] - kappa for row in test_exc]
                nonvacuous = bool(train_exc) and bool(test_exc)
                level_equivalence = all(
                    (row["gamma"] >= threshold)
                    == (row["potential"] >= compact_threshold - 1.0e-12)
                    for row in train + test
                )
                audits.append({
                    "currency": currency,
                    "gamma_threshold": threshold,
                    "compact_potential_threshold": compact_threshold,
                    "kappa": kappa,
                    "training_excursion_count": len(train_exc),
                    "holdout_excursion_count": len(test_exc),
                    "nonvacuous_excursion_test": nonvacuous,
                    "gamma_compact_level_equivalence": level_equivalence,
                    "training_minimum_currency_minus_kappa": (
                        min(train_margins) if train_margins else None
                    ),
                    "holdout_minimum_currency_minus_kappa": (
                        min(test_margins) if test_margins else None
                    ),
                    "heldout_danger_forces_compact_escape": (
                        nonvacuous and all(margin >= -1.0e-10 for margin in test_margins)
                    ),
                })
    observed = sorted({row["cutoff"] for row in rows})
    missing_cutoffs = sorted(set(required_cutoffs) - set(observed))
    by_currency = {
        currency: any(
            audit["currency"] == currency
            and audit["heldout_danger_forces_compact_escape"]
            for audit in audits
        )
        for currency in COMPACT_CURRENCIES
    }
    return {
        "required_cutoffs": list(required_cutoffs),
        "observed_cutoffs": observed,
        "missing_required_cutoffs": missing_cutoffs,
        "matched_cutoff_set_complete": not missing_cutoffs,
        "holdout_trajectories": sorted(holdout),
        "parameter_audits": audits,
        "currency_has_nonvacuous_heldout_compact_escape": by_currency,
        "any_compact_escape_currency_passes_heldout": any(by_currency.values()),
    }


def audit(
    residence_payload: dict[str, Any],
    thresholds: tuple[float, ...],
    kappas: tuple[float, ...],
    required_cutoffs: tuple[int, ...],
    holdout_trajectories: tuple[str, ...] = (),
    *,
    positive_part_relative_floor: float = 1.0e-10,
) -> dict[str, Any]:
    checkpoints = residence_payload.get("checkpoints")
    if not isinstance(checkpoints, list) or not checkpoints:
        raise ValueError("residence payload has no checkpoints")
    enriched: list[dict[str, Any]] = []
    rows: list[dict[str, Any]] = []
    for position, checkpoint in enumerate(checkpoints):
        if "time" not in checkpoint or "source_state" not in checkpoint:
            raise ValueError("every checkpoint must carry time and source_state")
        time = float(checkpoint["time"])
        raw_hat, nu, state_time = load_raw_state(Path(str(checkpoint["source_state"])))
        if state_time is not None and not math.isclose(state_time, time, abs_tol=1.0e-12):
            raise ValueError("checkpoint and NPZ times disagree")
        snapshot = compact_gamma_snapshot(
            raw_hat,
            nu,
            int(checkpoint["target_shell"]),
            positive_part_relative_floor=positive_part_relative_floor,
        )
        declared_gamma = checkpoint.get("gamma")
        if declared_gamma is not None and not math.isclose(
            float(declared_gamma), float(snapshot["gamma"]), rel_tol=1.0e-9, abs_tol=1.0e-12
        ):
            raise ValueError("declared Gamma does not match compact-potential reconstruction")
        output = dict(checkpoint)
        output["compact_gamma_potential_audit"] = snapshot
        output["truth_authority"] = False
        output["theorem_authority"] = False
        output["promoted"] = False
        enriched.append(output)
        branch_resolved = snapshot["positive_part_branch"] != "positive_part_kink_unresolved"
        one_sided = snapshot["one_sided_rates"]
        currencies = snapshot["candidate_signed_escape_currencies"]
        if branch_resolved and all(value is not None for value in currencies.values()):
            rows.append({
                "trajectory_id": str(checkpoint.get("trajectory_id", "aggregate-trajectory")),
                "checkpoint_index": int(checkpoint.get("checkpoint_index", position)),
                "time": time,
                "cutoff": int(checkpoint.get("cutoff", raw_hat.shape[0])),
                "gamma": float(snapshot["gamma"]),
                "tight": bool(checkpoint.get("packet_tight", False)),
                "branch_resolved": True,
                "parabolic_rate": float(snapshot["parabolic_rate"]),
                "potential": float(snapshot["compact_gamma_potential_B"]),
                "potential_derivative": float(snapshot["compact_derivative_parabolic"]),
                "depletion": float(one_sided["depletion"]),
                "replenishment": float(one_sided["replenishment"]),
                "currencies": {
                    name: float(currencies[name]) for name in COMPACT_CURRENCIES
                },
            })
    _chronological_groups(rows)
    integrals = integrate_bounded_potential_rows(rows, thresholds)
    validation = validate_compact_escape(
        rows, thresholds, kappas, required_cutoffs, holdout_trajectories
    )
    return {
        "schema_version": "1.0.0",
        "authority": {
            "exact_finite_galerkin_compact_derivative": True,
            "positive_part_kink_failed_closed": True,
            "bounded_one_sided_accounting_checked": True,
            "danger_forces_compact_escape": False,
            "cutoff_uniform_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "Q_K": "signed target-packet nonlinear transfer",
            "D_K": "target-packet Fourier dissipation sum",
            "Gamma_K": "Q_K,+/(2 nu D_K)",
            "compact_potential_B_K": "Q_K,+/(Q_K,++2 nu D_K)=Gamma_K/(1+Gamma_K)",
            "depletion": "max(-dB_K/dtau,0)",
            "replenishment": "max(dB_K/dtau,0)",
        },
        "currency_names": list(COMPACT_CURRENCIES),
        "checkpoints": enriched,
        "trajectory_bounded_budgets": integrals,
        "heldout_compact_escape_validation": validation,
        "limitations": [
            "the positive-part kink is excluded from classical derivative claims",
            "compact Gamma is tied to transfer danger but its replenishment still needs analytic absorption",
            "finite N32/N48/N64 agreement is not cutoff-uniform compactness",
            "one matched triad family is not a universal dangerous-transfer theorem",
            "no BKM, global-regularity, or Clay promotion",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--residence-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--gamma-thresholds", default="0.5,0.9,1.0")
    parser.add_argument("--kappa-candidates", default="0.01,0.05,0.1,0.25")
    parser.add_argument("--required-cutoffs", default="32,48,64")
    parser.add_argument("--holdout-trajectory", action="append", default=[])
    parser.add_argument("--positive-part-relative-floor", type=float, default=1.0e-10)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    result = audit(
        json.loads(args.residence_json.read_text(encoding="utf-8")),
        parse_floats(args.gamma_thresholds),
        parse_floats(args.kappa_candidates),
        parse_ints(args.required_cutoffs),
        tuple(args.holdout_trajectory),
        positive_part_relative_floor=args.positive_part_relative_floor,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "matched_cutoff_set_complete": result["heldout_compact_escape_validation"]["matched_cutoff_set_complete"],
        "any_compact_escape_currency_passes_heldout": result["heldout_compact_escape_validation"]["any_compact_escape_currency_passes_heldout"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
