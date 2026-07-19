#!/usr/bin/env python3
"""Stress-test compact-Gamma absorption on evolved angularly diffuse packets.

The earlier compact-Gamma lane used one isolated reality-closed triad.  This
script moves to finite packets made from several rotated copies of the same
exact triad geometry.  The copies have disjoint Fourier support up to reality
closure, distinct target directions, and optional phase dispersion.  The same
physical packet is represented at every cutoff and evolved by the repository's
Galerkin RK4 solver.

For every resolved state and target shell it computes

    B_K = Q_{K,+} / (Q_{K,+} + 2 nu D_K),

    E_K = sum_j max(-B_dot,j, 0),
    R_K = sum_j max( B_dot,j, 0),

and audits the sampled inequalities

    Gamma_K >= lambda  ->  E_K >= c_lambda,
    R_K <= theta E_K, theta < 1.

The output is finite-Galerkin evidence only.  Matched cutoffs and shells do not
establish a cutoff-uniform theorem, compactness, BKM control, or Clay authority.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import tempfile
from pathlib import Path
from typing import Any

import numpy as np

from ns_compact_gamma_potential_audit import compact_gamma_snapshot
from ns_compact_gamma_replenishment_audit import mechanism_accounting
from ns_depletion_currency_audit import parse_floats, parse_ints
from ns_galerkin_coherence_core import (
    frequency_grid,
    leray_project_hat,
    packet_mask,
)
from ns_generate_matched_galerkin_trajectories import rk4, stable_dt

BASE_P = np.asarray((3, 0, 1), dtype=int)
BASE_Q = np.asarray((0, 3, 1), dtype=int)
BASE_K = np.asarray((3, 3, 2), dtype=int)
BASE_VP = np.asarray((0.0, 1.0, 0.0))
BASE_VQ = np.asarray((1.0, 0.0, 0.0))
BASE_VK = np.asarray((6.0, 6.0, -18.0)) / 11.0


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


def _projective_mode_key(mode: np.ndarray | tuple[int, int, int]) -> tuple[int, int, int]:
    values = tuple(int(value) for value in mode)
    for value in values:
        if value > 0:
            return values
        if value < 0:
            return tuple(-entry for entry in values)
    return values


def signed_permutation_matrices() -> tuple[np.ndarray, ...]:
    matrices: list[np.ndarray] = []
    for permutation in itertools.permutations(range(3)):
        for signs in itertools.product((-1, 1), repeat=3):
            matrix = np.zeros((3, 3), dtype=int)
            for row, column in enumerate(permutation):
                matrix[row, column] = signs[row]
            matrices.append(matrix)
    identity = np.eye(3, dtype=int)
    matrices.sort(
        key=lambda matrix: (
            0 if np.array_equal(matrix, identity) else 1,
            tuple(int(value) for value in matrix.ravel()),
        )
    )
    return tuple(matrices)


def disjoint_orientations(count: int, scale: int) -> tuple[np.ndarray, ...]:
    if count < 1:
        raise ValueError("triad count must be positive")
    selected: list[np.ndarray] = []
    used: set[tuple[int, int, int]] = set()
    for matrix in signed_permutation_matrices():
        support = {
            _projective_mode_key(matrix @ (scale * BASE_P)),
            _projective_mode_key(matrix @ (scale * BASE_Q)),
            _projective_mode_key(matrix @ (scale * BASE_K)),
        }
        if support & used:
            continue
        selected.append(matrix)
        used.update(support)
        if len(selected) == count:
            return tuple(selected)
    raise ValueError(f"could not find {count} support-disjoint triad orientations")


def multitriad_diffuse_hat(
    n: int,
    target_shell: int,
    *,
    triad_count: int,
    input_amplitude: float,
    target_ratio: float,
    satellite_fraction: float,
    phase_spread: float,
    seed: int,
) -> tuple[np.ndarray, dict[str, Any]]:
    """Construct a reality-closed, divergence-free angularly diffuse packet.

    Shell 2 uses the original p+q=k triad.  Higher shells use dyadic copies, so
    the dimensionless geometry is shared across shells.  The first orientation
    is an exact dangerous anchor; the remaining orientations are weaker diffuse
    satellites with deterministic random amplitude and phase perturbations.
    """
    if target_shell < 2:
        raise ValueError("target shell must be at least 2")
    if input_amplitude <= 0.0 or target_ratio <= 0.0:
        raise ValueError("amplitudes must be positive")
    if not 0.0 < satellite_fraction <= 1.0:
        raise ValueError("satellite fraction must lie in (0,1]")
    if phase_spread < 0.0:
        raise ValueError("phase spread must be nonnegative")

    scale_factor = 2 ** (target_shell - 2)
    orientations = disjoint_orientations(triad_count, scale_factor)
    largest_component = max(
        int(np.max(np.abs(matrix @ (scale_factor * BASE_K))))
        for matrix in orientations
    )
    if largest_component >= n / 3.0:
        raise ValueError(
            f"cutoff N={n} does not dealiase shell-{target_shell} packet"
        )

    raw = np.zeros((n, n, n, 3), dtype=np.complex128)
    fft_scale = float(n ** 3)
    rng = np.random.default_rng(seed)
    triads: list[dict[str, Any]] = []

    def put(mode: np.ndarray, coefficient: np.ndarray) -> None:
        x, y, z = (int(value) for value in mode)
        raw[z % n, y % n, x % n] += fft_scale * coefficient
        raw[(-z) % n, (-y) % n, (-x) % n] += fft_scale * np.conjugate(coefficient)

    for index, matrix in enumerate(orientations):
        p = matrix @ (scale_factor * BASE_P)
        q = matrix @ (scale_factor * BASE_Q)
        k = matrix @ (scale_factor * BASE_K)
        vp = matrix @ BASE_VP
        vq = matrix @ BASE_VQ
        vk = matrix @ BASE_VK
        if index == 0:
            strength = 1.0
            phase = -0.5 * math.pi
            input_ratio = 1.0
        else:
            strength = satellite_fraction * (0.8 + 0.4 * float(rng.random()))
            phase = -0.5 * math.pi + float(rng.normal(0.0, phase_spread))
            input_ratio = 0.85 + 0.3 * float(rng.random())
        put(p, input_amplitude * strength * vp)
        put(q, input_amplitude * strength * input_ratio * vq)
        put(
            k,
            input_amplitude
            * target_ratio
            * strength
            * np.exp(1j * phase)
            * vk,
        )
        triads.append(
            {
                "index": index,
                "p": [int(value) for value in p],
                "q": [int(value) for value in q],
                "k": [int(value) for value in k],
                "strength": strength,
                "input_ratio": input_ratio,
                "target_phase": phase,
                "target_phase_over_pi": phase / math.pi,
            }
        )

    wave, norm_sq, _norm, dealias = frequency_grid(n)
    retained = leray_project_hat(raw * dealias[..., None], wave, norm_sq)
    return retained, {
        "target_shell": target_shell,
        "scale_factor": scale_factor,
        "triad_count": triad_count,
        "input_amplitude": input_amplitude,
        "target_ratio": target_ratio,
        "satellite_fraction": satellite_fraction,
        "phase_spread": phase_spread,
        "seed": seed,
        "triads": triads,
    }


def angular_packet_metrics(raw_hat: np.ndarray, target_shell: int) -> dict[str, Any]:
    n = int(raw_hat.shape[0])
    wave, norm_sq, norm, dealias = frequency_grid(n)
    retained = leray_project_hat(raw_hat * dealias[..., None], wave, norm_sq)
    packet = packet_mask(norm, target_shell, dealias)
    field = retained / float(n ** 3)
    energy = np.sum(np.abs(field) ** 2, axis=-1)
    packet_energy = float(np.sum(energy[packet]))
    total_energy = float(np.sum(energy[dealias]))
    if packet_energy <= 1.0e-30:
        raise ValueError("target packet has zero energy")
    active = packet & (energy > max(float(np.max(energy[packet])) * 1.0e-12, 1.0e-30))
    directions = wave[active] / norm[active, None]
    weights = energy[active]
    second_moment = np.einsum(
        "n,ni,nj->ij", weights, directions, directions
    ) / float(np.sum(weights))
    eigenvalues = np.linalg.eigvalsh(second_moment)
    participation = 1.0 / float(np.sum(eigenvalues * eigenvalues))
    isotropy_defect = float(np.linalg.norm(second_moment - np.eye(3) / 3.0))
    projective_modes = {
        _projective_mode_key(tuple(int(round(value)) for value in vector))
        for vector in wave[active]
    }
    divergence = np.einsum("...i,...i->...", wave, retained)
    retained_norm = float(np.max(np.abs(retained)))
    return {
        "packet_energy": packet_energy,
        "total_energy": total_energy,
        "packet_energy_fraction": packet_energy / max(total_energy, 1.0e-30),
        "direction_second_moment": second_moment.tolist(),
        "direction_eigenvalues": [float(value) for value in eigenvalues],
        "angular_participation_dimension": participation,
        "angular_isotropy_defect": isotropy_defect,
        "active_mode_count": int(np.count_nonzero(active)),
        "active_projective_mode_count": len(projective_modes),
        "relative_divergence_residual": float(np.max(np.abs(divergence)))
        / max(retained_norm, 1.0e-30),
    }


def evolved_states(
    raw_hat: np.ndarray,
    nu: float,
    target_shell: int,
    *,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
) -> list[dict[str, Any]]:
    if end_parabolic_time < 0.0:
        raise ValueError("end parabolic time must be nonnegative")
    if output_count < 1:
        raise ValueError("output count must be positive")
    rate = nu * float(2 ** (2 * target_shell))
    parabolic_targets = np.linspace(0.0, end_parabolic_time, output_count)
    physical_targets = parabolic_targets / rate
    state = np.asarray(raw_hat, dtype=np.complex128).copy()
    physical_time = 0.0
    physical_end = float(physical_targets[-1])
    max_dt = physical_end / max(8, 4 * max(output_count - 1, 1)) if physical_end > 0 else 1.0
    outputs: list[dict[str, Any]] = []
    for parabolic_time, target_time in zip(parabolic_targets, physical_targets):
        target = float(target_time)
        steps = 0
        while physical_time < target - 1.0e-14:
            dt = min(stable_dt(state, nu, cfl, max_dt), target - physical_time)
            if not math.isfinite(dt) or dt <= 0.0:
                raise RuntimeError("nonpositive Galerkin integration step")
            state = rk4(state, dt, nu)
            physical_time += dt
            steps += 1
            if steps > 100000:
                raise RuntimeError("Galerkin integration step limit exceeded")
        outputs.append(
            {
                "parabolic_time": float(parabolic_time),
                "physical_time": physical_time,
                "raw_hat": state.copy(),
                "steps_since_previous_output": steps,
            }
        )
    return outputs


def state_row(
    raw_hat: np.ndarray,
    *,
    cutoff: int,
    target_shell: int,
    nu: float,
    gamma_threshold: float,
    candidate_id: str,
    parabolic_time: float,
    physical_time: float,
    constructor: dict[str, Any],
) -> dict[str, Any]:
    snapshot = compact_gamma_snapshot(raw_hat, nu, target_shell)
    resolved = snapshot["positive_part_branch"] != "positive_part_kink_unresolved"
    accounting = mechanism_accounting(snapshot) if resolved else None
    angular = angular_packet_metrics(raw_hat, target_shell)
    gamma = float(snapshot["gamma"])
    return {
        "candidate_id": candidate_id,
        "cutoff": cutoff,
        "target_shell": target_shell,
        "parabolic_time": parabolic_time,
        "physical_time": physical_time,
        "gamma_threshold": gamma_threshold,
        "gamma": gamma,
        "dangerous": resolved and gamma >= gamma_threshold,
        "compact_potential": float(snapshot["compact_gamma_potential_B"]),
        "positive_part_branch": snapshot["positive_part_branch"],
        "mechanism_accounting": accounting,
        "angular_packet_metrics": angular,
        "finite_difference_residual": snapshot["finite_difference_check"]["residual"],
        "component_sum_residuals": snapshot["component_sum_residuals"],
        "constructor": constructor,
    }


def _configuration_id(
    seed: int,
    triad_count: int,
    phase_spread: float,
    target_ratio: float,
) -> str:
    return (
        f"seed-{seed}-triads-{triad_count}-"
        f"spread-{phase_spread:.6g}-ratio-{target_ratio:.6g}"
    )


def audit_family(
    *,
    search_cutoff: int,
    verify_cutoffs: tuple[int, ...],
    target_shells: tuple[int, ...],
    nu: float,
    input_amplitude: float,
    triad_counts: tuple[int, ...],
    phase_spreads: tuple[float, ...],
    target_ratios: tuple[float, ...],
    satellite_fraction: float,
    seeds: tuple[int, ...],
    gamma_threshold: float,
    minimum_angular_participation: float,
    verify_count: int,
    end_parabolic_time: float,
    output_count: int,
    cfl: float,
) -> dict[str, Any]:
    if verify_count < 1:
        raise ValueError("verify count must be positive")
    configurations = [
        {
            "candidate_id": _configuration_id(seed, triad_count, phase_spread, target_ratio),
            "seed": seed,
            "triad_count": triad_count,
            "phase_spread": phase_spread,
            "target_ratio": target_ratio,
        }
        for seed in seeds
        for triad_count in triad_counts
        for phase_spread in phase_spreads
        for target_ratio in target_ratios
    ]

    search_rows: list[dict[str, Any]] = []
    configuration_rows: dict[str, list[dict[str, Any]]] = {}
    for configuration in configurations:
        candidate_id = str(configuration["candidate_id"])
        rows: list[dict[str, Any]] = []
        for shell in target_shells:
            raw, constructor = multitriad_diffuse_hat(
                search_cutoff,
                shell,
                triad_count=int(configuration["triad_count"]),
                input_amplitude=input_amplitude,
                target_ratio=float(configuration["target_ratio"]),
                satellite_fraction=satellite_fraction,
                phase_spread=float(configuration["phase_spread"]),
                seed=int(configuration["seed"]),
            )
            row = state_row(
                raw,
                cutoff=search_cutoff,
                target_shell=shell,
                nu=nu,
                gamma_threshold=gamma_threshold,
                candidate_id=candidate_id,
                parabolic_time=0.0,
                physical_time=0.0,
                constructor=constructor,
            )
            rows.append(row)
            search_rows.append(row)
        configuration_rows[candidate_id] = rows

    admissible_configurations: list[dict[str, Any]] = []
    for configuration in configurations:
        candidate_id = str(configuration["candidate_id"])
        rows = configuration_rows[candidate_id]
        resolved = all(row["mechanism_accounting"] is not None for row in rows)
        angular = all(
            row["angular_packet_metrics"]["angular_participation_dimension"]
            >= minimum_angular_participation
            for row in rows
        )
        dangerous = all(bool(row["dangerous"]) for row in rows)
        if not (resolved and angular and dangerous):
            continue
        ratios = [
            row["mechanism_accounting"]["replenishment_over_escape"]
            for row in rows
        ]
        finite_ratios = [float(value) for value in ratios if value is not None]
        if len(finite_ratios) != len(rows):
            score = math.inf
        else:
            score = max(finite_ratios)
        admissible_configurations.append(
            {
                **configuration,
                "search_rows": rows,
                "worst_shell_replenishment_over_escape": score,
                "minimum_shell_escape_supply": min(
                    float(row["mechanism_accounting"]["escape_supply"])
                    for row in rows
                ),
                "minimum_shell_angular_participation": min(
                    float(
                        row["angular_packet_metrics"][
                            "angular_participation_dimension"
                        ]
                    )
                    for row in rows
                ),
            }
        )

    ranked = sorted(
        admissible_configurations,
        key=lambda row: (
            -float(row["worst_shell_replenishment_over_escape"]),
            float(row["minimum_shell_escape_supply"]),
        ),
    )
    selected = ranked[:verify_count]
    verification_rows: list[dict[str, Any]] = []
    selected_receipts: list[dict[str, Any]] = []

    for selected_index, configuration in enumerate(selected):
        candidate_id = str(configuration["candidate_id"])
        candidate_rows: list[dict[str, Any]] = []
        for shell in target_shells:
            for cutoff in verify_cutoffs:
                raw, constructor = multitriad_diffuse_hat(
                    cutoff,
                    shell,
                    triad_count=int(configuration["triad_count"]),
                    input_amplitude=input_amplitude,
                    target_ratio=float(configuration["target_ratio"]),
                    satellite_fraction=satellite_fraction,
                    phase_spread=float(configuration["phase_spread"]),
                    seed=int(configuration["seed"]),
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
                    row = state_row(
                        state["raw_hat"],
                        cutoff=cutoff,
                        target_shell=shell,
                        nu=nu,
                        gamma_threshold=gamma_threshold,
                        candidate_id=candidate_id,
                        parabolic_time=float(state["parabolic_time"]),
                        physical_time=float(state["physical_time"]),
                        constructor=constructor,
                    )
                    row["steps_since_previous_output"] = int(
                        state["steps_since_previous_output"]
                    )
                    candidate_rows.append(row)
                    verification_rows.append(row)
        selected_receipts.append(
            {
                "selected_index": selected_index,
                "configuration": {
                    key: value
                    for key, value in configuration.items()
                    if key not in {"search_rows"}
                },
                "row_count": len(candidate_rows),
                "rows": candidate_rows,
            }
        )

    dangerous_rows = [row for row in verification_rows if row["dangerous"]]
    evolved_dangerous_rows = [
        row for row in dangerous_rows if float(row["parabolic_time"]) > 0.0
    ]
    theta_values = [
        float(row["mechanism_accounting"]["replenishment_over_escape"])
        for row in dangerous_rows
        if row["mechanism_accounting"]["replenishment_over_escape"] is not None
    ]
    escape_values = [
        float(row["mechanism_accounting"]["escape_supply"])
        for row in dangerous_rows
    ]
    unabsorbed = [
        row
        for row in dangerous_rows
        if row["mechanism_accounting"]["strict_absorption_margin"] <= 0.0
        or row["mechanism_accounting"]["escape_supply"] <= 0.0
    ]

    matched_groups: list[dict[str, Any]] = []
    group_map: dict[tuple[str, int, float], list[dict[str, Any]]] = {}
    for row in verification_rows:
        key = (
            str(row["candidate_id"]),
            int(row["target_shell"]),
            float(row["parabolic_time"]),
        )
        group_map.setdefault(key, []).append(row)
    for (candidate_id, shell, parabolic_time), rows in sorted(group_map.items()):
        rows.sort(key=lambda row: int(row["cutoff"]))
        gammas = [float(row["gamma"]) for row in rows]
        ratios = [
            row["mechanism_accounting"]["replenishment_over_escape"]
            for row in rows
            if row["mechanism_accounting"] is not None
        ]
        finite_ratios = [float(value) for value in ratios if value is not None]
        matched_groups.append(
            {
                "candidate_id": candidate_id,
                "target_shell": shell,
                "parabolic_time": parabolic_time,
                "observed_cutoffs": [int(row["cutoff"]) for row in rows],
                "matched_cutoff_complete": set(int(row["cutoff"]) for row in rows)
                == set(verify_cutoffs),
                "gamma_spread": max(gammas) - min(gammas),
                "theta_spread": (
                    max(finite_ratios) - min(finite_ratios)
                    if finite_ratios
                    else None
                ),
                "all_rows_dangerous": all(bool(row["dangerous"]) for row in rows),
                "all_dangerous_rows_strictly_absorbed": all(
                    (not row["dangerous"])
                    or (
                        row["mechanism_accounting"] is not None
                        and row["mechanism_accounting"]["strict_absorption_margin"]
                        > 0.0
                    )
                    for row in rows
                ),
            }
        )

    finite_difference_residuals = [
        float(row["finite_difference_residual"])
        for row in verification_rows
        if row["finite_difference_residual"] is not None
    ]
    mechanism_residuals = [
        float(row["mechanism_accounting"]["mechanism_balance_residual"])
        for row in verification_rows
        if row["mechanism_accounting"] is not None
    ]
    angular_participations = [
        float(row["angular_packet_metrics"]["angular_participation_dimension"])
        for row in verification_rows
    ]
    divergence_residuals = [
        float(row["angular_packet_metrics"]["relative_divergence_residual"])
        for row in verification_rows
    ]
    theta_envelope = max(theta_values) if theta_values else None
    c_lambda = min(escape_values) if escape_values else None
    matched_complete = bool(matched_groups) and all(
        group["matched_cutoff_complete"] for group in matched_groups
    )
    initial_groups = [
        group for group in matched_groups if abs(float(group["parabolic_time"])) <= 1.0e-15
    ]
    sampled_uniform_candidate = (
        bool(dangerous_rows)
        and bool(evolved_dangerous_rows)
        and not unabsorbed
        and theta_envelope is not None
        and theta_envelope < 1.0
        and c_lambda is not None
        and c_lambda > 0.0
        and matched_complete
        and len(initial_groups) == len(selected) * len(target_shells)
        and all(group["all_rows_dangerous"] for group in initial_groups)
    )

    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_multitriad_audit": True,
            "angularly_diffuse_packet_audit": True,
            "evolved_packet_audit": True,
            "matched_shell_cutoff_sampling": True,
            "sampled_uniform_candidate_survives": sampled_uniform_candidate,
            "cutoff_shell_uniform_authority": False,
            "continuum_compactness_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "angular_participation_dimension": "inverse Frobenius square of the normalized direction second moment; range [1,3]",
            "escape_supply": "sum of negative compact-Gamma mechanism derivatives",
            "replenishment": "sum of positive compact-Gamma mechanism derivatives",
            "sampled_theta_envelope": "maximum R_K/E_K over sampled dangerous rows",
            "sampled_c_lambda": "minimum E_K over sampled dangerous rows",
        },
        "parameters": {
            "search_cutoff": search_cutoff,
            "verify_cutoffs": list(verify_cutoffs),
            "target_shells": list(target_shells),
            "viscosity": nu,
            "input_amplitude": input_amplitude,
            "triad_counts": list(triad_counts),
            "phase_spreads": list(phase_spreads),
            "target_ratios": list(target_ratios),
            "satellite_fraction": satellite_fraction,
            "seeds": list(seeds),
            "gamma_threshold": gamma_threshold,
            "minimum_angular_participation": minimum_angular_participation,
            "verify_count": verify_count,
            "end_parabolic_time": end_parabolic_time,
            "output_count": output_count,
            "cfl": cfl,
        },
        "configuration_count": len(configurations),
        "search_row_count": len(search_rows),
        "admissible_configuration_count": len(admissible_configurations),
        "selected_configuration_count": len(selected),
        "selected_configurations": selected_receipts,
        "verification_row_count": len(verification_rows),
        "dangerous_row_count": len(dangerous_rows),
        "evolved_dangerous_row_count": len(evolved_dangerous_rows),
        "unabsorbed_dangerous_count": len(unabsorbed),
        "sampled_theta_envelope": theta_envelope,
        "sampled_absorption_margin": (
            1.0 - theta_envelope if theta_envelope is not None else None
        ),
        "sampled_c_lambda": c_lambda,
        "minimum_angular_participation": (
            min(angular_participations) if angular_participations else None
        ),
        "maximum_relative_divergence_residual": (
            max(divergence_residuals) if divergence_residuals else None
        ),
        "maximum_mechanism_balance_residual": (
            max(mechanism_residuals) if mechanism_residuals else None
        ),
        "maximum_finite_difference_residual": (
            max(finite_difference_residuals)
            if finite_difference_residuals
            else None
        ),
        "matched_cutoff_groups": matched_groups,
        "maximum_matched_gamma_spread": (
            max(float(group["gamma_spread"]) for group in matched_groups)
            if matched_groups
            else None
        ),
        "maximum_matched_theta_spread": (
            max(
                float(group["theta_spread"])
                for group in matched_groups
                if group["theta_spread"] is not None
            )
            if any(group["theta_spread"] is not None for group in matched_groups)
            else None
        ),
        "top_search_configurations": ranked[: min(20, len(ranked))],
        "limitations": [
            "finite rotated-triad packet family only",
            "short Galerkin evolution only",
            "sampled theta and c_lambda are not analytic constants",
            "matched shells and cutoffs do not prove uniformity",
            "no continuum compactness, BKM, global-regularity, or Clay promotion",
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
    parser.add_argument("--triad-counts", default="2,4")
    parser.add_argument("--phase-spreads", default="0.0,0.35")
    parser.add_argument("--target-ratios", default="2.5")
    parser.add_argument("--satellite-fraction", type=float, default=0.55)
    parser.add_argument("--seeds", default="0,1")
    parser.add_argument("--gamma-threshold", type=float, default=0.5)
    parser.add_argument("--minimum-angular-participation", type=float, default=1.3)
    parser.add_argument("--verify-count", type=int, default=1)
    parser.add_argument("--end-parabolic-time", type=float, default=0.002)
    parser.add_argument("--output-count", type=int, default=2)
    parser.add_argument("--cfl", type=float, default=0.2)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    result = audit_family(
        search_cutoff=args.search_cutoff,
        verify_cutoffs=parse_ints(args.verify_cutoffs),
        target_shells=parse_ints(args.target_shells),
        nu=args.viscosity,
        input_amplitude=args.input_amplitude,
        triad_counts=parse_ints(args.triad_counts),
        phase_spreads=parse_floats(args.phase_spreads),
        target_ratios=parse_floats(args.target_ratios),
        satellite_fraction=args.satellite_fraction,
        seeds=parse_ints(args.seeds),
        gamma_threshold=args.gamma_threshold,
        minimum_angular_participation=args.minimum_angular_participation,
        verify_count=args.verify_count,
        end_parabolic_time=args.end_parabolic_time,
        output_count=args.output_count,
        cfl=args.cfl,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(
        json.dumps(
            {
                "output_json": str(args.output_json),
                "selected_configuration_count": result[
                    "selected_configuration_count"
                ],
                "dangerous_row_count": result["dangerous_row_count"],
                "evolved_dangerous_row_count": result[
                    "evolved_dangerous_row_count"
                ],
                "sampled_theta_envelope": result["sampled_theta_envelope"],
                "sampled_c_lambda": result["sampled_c_lambda"],
                "sampled_uniform_candidate_survives": result["authority"][
                    "sampled_uniform_candidate_survives"
                ],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
