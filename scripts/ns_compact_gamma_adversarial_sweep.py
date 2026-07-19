#!/usr/bin/env python3
"""Search phase/amplitude triad families for compact-Gamma counterexamples.

The matched baseline found strong signed decay of

    B_K = Gamma_K/(1+Gamma_K)

on one positive-transfer triad.  This script does not treat that trajectory as
representative.  It sweeps the target phase, input-amplitude ratio, and target
amplitude at a cheap search cutoff, then re-evaluates the most adverse dangerous
states at matched N32/N48/N64 cutoffs.

A dangerous state with dB/dtau >= 0 falsifies the pointwise implication
"danger implies signed compact escape" for this finite carrier.  A negative
result only leaves the candidate alive on the sampled family.
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

from ns_compact_gamma_potential_audit import compact_gamma_snapshot
from ns_depletion_currency_audit import parse_floats, parse_ints


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


def phased_triad_hat(
    n: int,
    input_amplitude: float,
    input_ratio: float,
    target_amplitude: float,
    target_phase: float,
) -> np.ndarray:
    """Reality-closed p+q=k triad with variable phase and amplitudes."""
    if n < 16:
        raise ValueError("triad sweep requires cutoff at least 16")
    if input_amplitude <= 0.0 or input_ratio <= 0.0 or target_amplitude <= 0.0:
        raise ValueError("amplitudes and ratio must be positive")
    raw = np.zeros((n, n, n, 3), dtype=np.complex128)
    scale = float(n ** 3)
    p = (3, 0, 1)
    q = (0, 3, 1)
    k = (3, 3, 2)
    vp = np.asarray((0.0, 1.0, 0.0))
    vq = np.asarray((1.0, 0.0, 0.0))
    vk = np.asarray((6.0, 6.0, -18.0)) / 11.0

    def put(mode: tuple[int, int, int], coefficient: np.ndarray) -> None:
        x, y, z = mode
        raw[z % n, y % n, x % n] = scale * coefficient
        raw[(-z) % n, (-y) % n, (-x) % n] = scale * np.conjugate(coefficient)

    put(p, input_amplitude * vp)
    put(q, input_amplitude * input_ratio * vq)
    put(k, target_amplitude * np.exp(1j * target_phase) * vk)
    return raw


def _row(
    n: int,
    nu: float,
    shell: int,
    input_amplitude: float,
    input_ratio: float,
    target_amplitude: float,
    target_phase: float,
) -> dict[str, Any]:
    raw = phased_triad_hat(
        n, input_amplitude, input_ratio, target_amplitude, target_phase
    )
    result = compact_gamma_snapshot(raw, nu, shell)
    return {
        "cutoff": n,
        "input_amplitude": input_amplitude,
        "input_ratio": input_ratio,
        "target_amplitude": target_amplitude,
        "target_phase": target_phase,
        "target_phase_over_pi": target_phase / math.pi,
        "gamma": result["gamma"],
        "compact_potential": result["compact_gamma_potential_B"],
        "compact_derivative_parabolic": result["compact_derivative_parabolic"],
        "positive_part_branch": result["positive_part_branch"],
        "currencies": result["candidate_signed_escape_currencies"],
        "grouped_derivatives": result["grouped_compact_derivatives_parabolic"],
        "finite_difference_residual": result["finite_difference_check"]["residual"],
        "component_sum_residuals": result["component_sum_residuals"],
    }


def sweep(
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
    if verify_count < 1:
        raise ValueError("verify-count must be positive")
    phases = tuple(-math.pi + 2.0 * math.pi * index / phase_count for index in range(phase_count))
    rows: list[dict[str, Any]] = []
    for ratio in input_ratios:
        for target in target_amplitudes:
            for phase in phases:
                rows.append(_row(
                    search_cutoff,
                    nu,
                    shell,
                    input_amplitude,
                    ratio,
                    target,
                    phase,
                ))
    resolved = [
        row for row in rows
        if row["positive_part_branch"] != "positive_part_kink_unresolved"
        and row["compact_derivative_parabolic"] is not None
    ]
    dangerous = [row for row in resolved if row["gamma"] >= gamma_threshold]
    adverse = sorted(
        dangerous,
        key=lambda row: (
            -float(row["compact_derivative_parabolic"]),
            -float(row["gamma"]),
        ),
    )
    selected = adverse[:verify_count]
    matched: list[dict[str, Any]] = []
    for candidate_index, candidate in enumerate(selected):
        verification = [
            _row(
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
        derivatives = [float(row["compact_derivative_parabolic"]) for row in verification]
        gammas = [float(row["gamma"]) for row in verification]
        matched.append({
            "candidate_index": candidate_index,
            "search_row": candidate,
            "matched_cutoff_rows": verification,
            "all_cutoffs_dangerous": all(gamma >= gamma_threshold for gamma in gammas),
            "all_cutoffs_non_depleting": all(value >= -1.0e-10 for value in derivatives),
            "minimum_compact_derivative_parabolic": min(derivatives),
            "maximum_compact_derivative_parabolic": max(derivatives),
            "gamma_spread": max(gammas) - min(gammas),
            "derivative_spread": max(derivatives) - min(derivatives),
        })

    pointwise_counterexamples = [
        row for row in dangerous
        if float(row["compact_derivative_parabolic"]) >= -1.0e-10
    ]
    matched_counterexamples = [
        row for row in matched
        if row["all_cutoffs_dangerous"] and row["all_cutoffs_non_depleting"]
    ]
    finite_residuals = [
        float(row["finite_difference_residual"])
        for row in resolved
        if row["finite_difference_residual"] is not None
    ]
    return {
        "schema_version": "1.0.0",
        "authority": {
            "finite_galerkin_adversarial_search": True,
            "universal_pointwise_implication_falsified": bool(matched_counterexamples),
            "universal_pointwise_implication_proved": False,
            "cutoff_uniform_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
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
        "pointwise_non_depleting_dangerous_count": len(pointwise_counterexamples),
        "matched_counterexample_count": len(matched_counterexamples),
        "minimum_dangerous_compact_derivative_parabolic": (
            min(float(row["compact_derivative_parabolic"]) for row in dangerous)
            if dangerous else None
        ),
        "maximum_dangerous_compact_derivative_parabolic": (
            max(float(row["compact_derivative_parabolic"]) for row in dangerous)
            if dangerous else None
        ),
        "minimum_dangerous_net_escape": (
            min(float(row["currencies"]["net_compact_gamma_escape"]) for row in dangerous)
            if dangerous else None
        ),
        "maximum_finite_difference_residual": max(finite_residuals) if finite_residuals else None,
        "matched_adverse_candidates": matched,
        "matched_counterexamples": matched_counterexamples,
        "top_adverse_search_rows": adverse[: min(20, len(adverse))],
        "limitations": [
            "finite phase/amplitude family only",
            "counterexample falsifies only the declared pointwise candidate implication",
            "absence of a sampled counterexample is not proof",
            "matched cutoffs do not establish continuum compactness",
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
    result = sweep(
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
        "matched_counterexample_count": result["matched_counterexample_count"],
        "universal_pointwise_implication_falsified": result["authority"]["universal_pointwise_implication_falsified"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
