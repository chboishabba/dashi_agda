#!/usr/bin/env python3
"""Measure escape-versus-replenishment for the compact-Gamma potential.

For the bounded transfer potential

    B_K = Q_{K,+}/(Q_{K,+}+2 nu D_K),

its exact Galerkin derivative is decomposed into target nonlinear, off-packet
nonlinear, and viscous contributions.  At each resolved dangerous state define

    E_K = sum_j max(-B_dot,j, 0),
    R_K = sum_j max( B_dot,j, 0).

Then B_dot = R_K-E_K.  This audit searches for a strict absorption factor

    R_K <= theta E_K,  theta < 1,

on a phase/amplitude triad family and verifies the worst sampled cases at
matched cutoffs.  The estimate is empirical and pointwise; no continuum or
cutoff-uniform conclusion is inferred.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import tempfile
from pathlib import Path
from typing import Any

from ns_compact_gamma_adversarial_sweep import phased_triad_hat
from ns_compact_gamma_potential_audit import compact_gamma_snapshot
from ns_depletion_currency_audit import parse_floats, parse_ints

MECHANISMS = ("target_nonlinear", "off_packet_nonlinear", "viscous")


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


def mechanism_accounting(snapshot: dict[str, Any]) -> dict[str, Any]:
    grouped = snapshot["grouped_compact_derivatives_parabolic"]
    contributions = {name: float(grouped[name]) for name in MECHANISMS}
    escape_by_mechanism = {
        name: max(-value, 0.0) for name, value in contributions.items()
    }
    replenishment_by_mechanism = {
        name: max(value, 0.0) for name, value in contributions.items()
    }
    escape = sum(escape_by_mechanism.values())
    replenishment = sum(replenishment_by_mechanism.values())
    derivative = snapshot["compact_derivative_parabolic"]
    if derivative is None:
        raise ValueError("mechanism accounting requires a resolved derivative branch")
    derivative = float(derivative)
    ratio = replenishment / escape if escape > 0.0 else None
    return {
        "signed_contributions": contributions,
        "escape_by_mechanism": escape_by_mechanism,
        "replenishment_by_mechanism": replenishment_by_mechanism,
        "escape_supply": escape,
        "replenishment": replenishment,
        "net_signed_derivative": derivative,
        "net_escape": max(-derivative, 0.0),
        "net_replenishment": max(derivative, 0.0),
        "replenishment_over_escape": ratio,
        "strict_absorption_margin": escape - replenishment,
        "mechanism_balance_residual": abs((replenishment - escape) - derivative),
    }


def _state_row(
    cutoff: int,
    nu: float,
    shell: int,
    input_amplitude: float,
    input_ratio: float,
    target_amplitude: float,
    target_phase: float,
) -> dict[str, Any]:
    raw = phased_triad_hat(
        cutoff,
        input_amplitude,
        input_ratio,
        target_amplitude,
        target_phase,
    )
    snapshot = compact_gamma_snapshot(raw, nu, shell)
    resolved = snapshot["positive_part_branch"] != "positive_part_kink_unresolved"
    accounting = mechanism_accounting(snapshot) if resolved else None
    return {
        "cutoff": cutoff,
        "input_amplitude": input_amplitude,
        "input_ratio": input_ratio,
        "target_amplitude": target_amplitude,
        "target_phase": target_phase,
        "target_phase_over_pi": target_phase / math.pi,
        "gamma": snapshot["gamma"],
        "compact_potential": snapshot["compact_gamma_potential_B"],
        "positive_part_branch": snapshot["positive_part_branch"],
        "mechanism_accounting": accounting,
        "finite_difference_residual": snapshot["finite_difference_check"]["residual"],
    }


def audit_family(
    *,
    search_cutoff: int,
    verify_cutoffs: tuple[int, ...],
    nu: float,
    shell: int,
    input_amplitude: float,
    input_ratios: tuple[float, ...],
    target_amplitudes: tuple[float, ...],
    phase_count: int,
    gamma_threshold: float,
    verify_count: int,
) -> dict[str, Any]:
    if phase_count < 4:
        raise ValueError("phase-count must be at least four")
    phases = tuple(
        -math.pi + 2.0 * math.pi * index / phase_count
        for index in range(phase_count)
    )
    rows = [
        _state_row(
            search_cutoff,
            nu,
            shell,
            input_amplitude,
            ratio,
            target,
            phase,
        )
        for ratio in input_ratios
        for target in target_amplitudes
        for phase in phases
    ]
    resolved = [row for row in rows if row["mechanism_accounting"] is not None]
    dangerous = [row for row in resolved if float(row["gamma"]) >= gamma_threshold]

    def absorption_key(row: dict[str, Any]) -> tuple[float, float]:
        accounting = row["mechanism_accounting"]
        ratio = accounting["replenishment_over_escape"]
        score = math.inf if ratio is None and accounting["replenishment"] > 0.0 else (ratio or 0.0)
        return (-score, accounting["strict_absorption_margin"])

    adverse = sorted(dangerous, key=absorption_key)
    selected = adverse[:verify_count]
    matched: list[dict[str, Any]] = []
    for index, candidate in enumerate(selected):
        verification = [
            _state_row(
                cutoff,
                nu,
                shell,
                input_amplitude,
                float(candidate["input_ratio"]),
                float(candidate["target_amplitude"]),
                float(candidate["target_phase"]),
            )
            for cutoff in verify_cutoffs
        ]
        ratios = [
            row["mechanism_accounting"]["replenishment_over_escape"]
            for row in verification
        ]
        finite_ratios = [float(value) for value in ratios if value is not None]
        margins = [
            float(row["mechanism_accounting"]["strict_absorption_margin"])
            for row in verification
        ]
        matched.append({
            "candidate_index": index,
            "search_row": candidate,
            "matched_cutoff_rows": verification,
            "all_cutoffs_dangerous": all(
                float(row["gamma"]) >= gamma_threshold for row in verification
            ),
            "all_cutoffs_strictly_absorbed": all(margin > 0.0 for margin in margins),
            "maximum_replenishment_over_escape": (
                max(finite_ratios) if finite_ratios else None
            ),
            "minimum_strict_absorption_margin": min(margins),
            "ratio_spread": (
                max(finite_ratios) - min(finite_ratios)
                if finite_ratios else None
            ),
        })

    finite_dangerous_ratios = [
        float(row["mechanism_accounting"]["replenishment_over_escape"])
        for row in dangerous
        if row["mechanism_accounting"]["replenishment_over_escape"] is not None
    ]
    unabsorbed = [
        row for row in dangerous
        if row["mechanism_accounting"]["strict_absorption_margin"] <= 0.0
    ]
    matched_unabsorbed = [
        row for row in matched
        if row["all_cutoffs_dangerous"] and not row["all_cutoffs_strictly_absorbed"]
    ]
    residuals = [
        float(row["mechanism_accounting"]["mechanism_balance_residual"])
        for row in resolved
    ]
    finite_difference_residuals = [
        float(row["finite_difference_residual"])
        for row in resolved
        if row["finite_difference_residual"] is not None
    ]
    theta_envelope = max(finite_dangerous_ratios) if finite_dangerous_ratios else None
    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_replenishment_audit": True,
            "sampled_strict_absorption_falsified": bool(matched_unabsorbed),
            "sampled_strict_absorption_survives": bool(dangerous) and not matched_unabsorbed,
            "cutoff_uniform_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definitions": {
            "escape_supply": "sum of negative compact-potential mechanism derivatives",
            "replenishment": "sum of positive compact-potential mechanism derivatives",
            "theta_emp": "replenishment/escape_supply",
            "strict_absorption": "theta_emp < 1",
        },
        "parameters": {
            "search_cutoff": search_cutoff,
            "verify_cutoffs": list(verify_cutoffs),
            "viscosity": nu,
            "target_shell": shell,
            "input_amplitude": input_amplitude,
            "input_ratios": list(input_ratios),
            "target_amplitudes": list(target_amplitudes),
            "phase_count": phase_count,
            "gamma_threshold": gamma_threshold,
            "verify_count": verify_count,
        },
        "search_row_count": len(rows),
        "resolved_row_count": len(resolved),
        "dangerous_row_count": len(dangerous),
        "unabsorbed_dangerous_count": len(unabsorbed),
        "matched_unabsorbed_count": len(matched_unabsorbed),
        "sampled_theta_envelope": theta_envelope,
        "sampled_absorption_margin": (
            1.0 - theta_envelope if theta_envelope is not None else None
        ),
        "minimum_dangerous_strict_absorption_margin": (
            min(
                float(row["mechanism_accounting"]["strict_absorption_margin"])
                for row in dangerous
            )
            if dangerous else None
        ),
        "maximum_mechanism_balance_residual": max(residuals) if residuals else None,
        "maximum_finite_difference_residual": (
            max(finite_difference_residuals)
            if finite_difference_residuals else None
        ),
        "matched_adverse_candidates": matched,
        "matched_unabsorbed_candidates": matched_unabsorbed,
        "top_adverse_search_rows": adverse[: min(20, len(adverse))],
        "limitations": [
            "pointwise finite-state absorption only",
            "a sampled theta envelope is not an analytic constant",
            "phase/amplitude triads do not exhaust divergence-free packets",
            "matched cutoffs do not establish compactness",
            "no BKM, global-regularity, or Clay promotion",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--search-cutoff", type=int, default=16)
    parser.add_argument("--verify-cutoffs", default="32,48,64")
    parser.add_argument("--viscosity", type=float, default=0.01)
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--input-amplitude", type=float, default=0.1)
    parser.add_argument("--input-ratios", default="0.5,1.0,2.0")
    parser.add_argument("--target-amplitudes", default="0.1,0.25,0.5")
    parser.add_argument("--phase-count", type=int, default=12)
    parser.add_argument("--gamma-threshold", type=float, default=0.5)
    parser.add_argument("--verify-count", type=int, default=3)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    result = audit_family(
        search_cutoff=args.search_cutoff,
        verify_cutoffs=parse_ints(args.verify_cutoffs),
        nu=args.viscosity,
        shell=args.target_shell,
        input_amplitude=args.input_amplitude,
        input_ratios=parse_floats(args.input_ratios),
        target_amplitudes=parse_floats(args.target_amplitudes),
        phase_count=args.phase_count,
        gamma_threshold=args.gamma_threshold,
        verify_count=args.verify_count,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "dangerous_row_count": result["dangerous_row_count"],
        "sampled_theta_envelope": result["sampled_theta_envelope"],
        "matched_unabsorbed_count": result["matched_unabsorbed_count"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
