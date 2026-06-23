#!/usr/bin/env python3
"""Tail/shell progression scan for matrix-free NS triad K_N(A).

This harness uses the iterative generalized eigensolver over the existing
matrix-free backend and reclassifies low-frame rows against moving radial tail
cutoffs.  It is deliberately candidate-only: GPU matvecs may accelerate the
scan, but neither GPU nor numerical receipts carry theorem authority.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
from ns_triad_cocycle_floor_scan import _validate_shells  # type: ignore
from ns_triad_constrained_adversarial_fork_optimizer import (  # type: ignore
    DEFAULT_D0,
    DEFAULT_R0,
    _candidate_profiles,
    _cube_modes,
    _normalize_profile,
    _profile_metrics,
    _shell_levels,
)
from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_ZERO_EPS,
    ERROR_STATUS,
    OK_STATUS,
    PARTIAL_STATUS,
    _build_frame_surface,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_triad_kn_iterative_generalized_eig import _evaluate  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_tail_progression_scan.py"
CONTRACT = "ns_triad_kn_tail_progression_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_TAIL_PROGRESSION_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_tail_progression_scan_N128_20260623.json"
)
DEFAULT_SHELLS = (4, 5)
DEFAULT_SEEDS = (0,)
DEFAULT_SAMPLE_COUNT = 4
DEFAULT_MIX_COUNT = 2
DEFAULT_C0_VALUES = (0.10, 0.25)
DEFAULT_TAIL_CUTOFFS = (3, 4, 5, 6, 8)
DEFAULT_TAIL_ETAS = (0.05, 0.10, 0.25, 0.40)
DEFAULT_D0_VALUES = (2.0, 2.5, 3.0, 4.0)
DEFAULT_PARITY_TOL = 1.0e-4
DEFAULT_LOBPCG_TOL = 1.0e-5
DEFAULT_LOBPCG_MAXITER = 40
DEFAULT_GENERALIZED_MASS_SHIFT = 1.0e-8

CONTROL_CARD = {
    "O": "Classify matrix-free K_N(A) low-frame rows by radial tail cutoff and shell progression.",
    "R": (
        "Use the iterative generalized eigensolver with CPU or Vulkan matvecs, then sweep "
        "K, eta, D0, and c0 to separate finite-shell degeneracy from asymptotic-tail danger."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; no theorem, full-NS, or Clay promotion is inferred.",
    "L": (
        "Load shell carriers, sample energy profiles, solve L_neg x = lambda L_abs x without "
        "dense reconstruction, compute tail masses, and classify branches against each threshold grid point."
    ),
    "P": ROUTE_DECISION,
    "G": "GPU matvec acceleration remains non-authoritative and gpu_kn_authority is always false.",
    "F": "This tests the remaining obstruction; it does not prove asymptotic-tail exclusion.",
}


def _parse_csv_numbers(value: str, cast: type[int] | type[float]) -> list[Any]:
    parsed: list[Any] = []
    for item in value.split(","):
        stripped = item.strip()
        if stripped:
            parsed.append(cast(stripped))
    if not parsed:
        raise argparse.ArgumentTypeError("must contain at least one value")
    return parsed


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--kn-backend", choices=("cpu-matrix-free", "vulkan-matvec"), default="cpu-matrix-free")
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=1)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--mix-count", type=int, default=DEFAULT_MIX_COUNT)
    parser.add_argument("--max-profiles-per-row", type=int, default=4)
    parser.add_argument("--profile-sample-limit", type=int, default=6)
    parser.add_argument("--seed", dest="seeds", action="append", type=int, default=None)
    parser.add_argument("--r0", type=float, default=DEFAULT_R0)
    parser.add_argument("--c0-values", type=lambda text: _parse_csv_numbers(text, float), default=list(DEFAULT_C0_VALUES))
    parser.add_argument("--tail-cutoffs", type=lambda text: _parse_csv_numbers(text, int), default=list(DEFAULT_TAIL_CUTOFFS))
    parser.add_argument("--tail-etas", type=lambda text: _parse_csv_numbers(text, float), default=list(DEFAULT_TAIL_ETAS))
    parser.add_argument("--d0-values", type=lambda text: _parse_csv_numbers(text, float), default=list(DEFAULT_D0_VALUES))
    parser.add_argument("--parity-tol", type=float, default=DEFAULT_PARITY_TOL)
    parser.add_argument("--lobpcg-tol", type=float, default=DEFAULT_LOBPCG_TOL)
    parser.add_argument("--lobpcg-maxiter", type=int, default=DEFAULT_LOBPCG_MAXITER)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--generalized-mass-shift", type=float, default=DEFAULT_GENERALIZED_MASS_SHIFT)
    parser.add_argument("--dense-oracle-shell-limit", type=int, default=3)
    parser.add_argument("--gpu-matvec-checks", type=int, default=1)
    parser.add_argument("--finite-shell-cutoff", type=int, default=3)
    parser.add_argument("--no-force-tail-profiles", action="store_true")
    parser.add_argument("--shell", dest="shells", action="append", type=int, default=None)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _tail_mass(shell_levels: np.ndarray, probability: np.ndarray, cutoff: int) -> float:
    shells = np.asarray(shell_levels, dtype=np.float64)
    p = np.asarray(probability, dtype=np.float64)
    return float(np.sum(p[shells >= float(cutoff)]))


def _radial_max_with_mass_eta(shell_levels: np.ndarray, probability: np.ndarray, eta: float) -> int | None:
    shells = np.asarray(shell_levels, dtype=np.float64)
    p = np.asarray(probability, dtype=np.float64)
    shell_mass: dict[int, float] = {}
    for shell_value, mass in zip(shells, p, strict=False):
        shell = int(shell_value)
        shell_mass[shell] = shell_mass.get(shell, 0.0) + float(mass)
    active = [shell for shell, mass in shell_mass.items() if mass >= float(eta)]
    if len(active) == 0:
        return None
    return int(max(active))


def _classify_tail(
    *,
    lambda_min: Any,
    metrics: dict[str, Any],
    worst_shell: Any,
    c0: float,
    r0: float,
    cutoff: int,
    eta: float,
    d0: float,
    finite_shell_cutoff: int,
) -> str:
    if not isinstance(lambda_min, (int, float)) or not math.isfinite(float(lambda_min)):
        return "unavailable"
    if float(lambda_min) >= float(c0):
        return "frame-coercive"
    dissipation = float(metrics["dissipation_proxy"])
    if dissipation > float(d0):
        return "high-dissipation"
    high_tail = float(metrics["high_shell_mass_by_cutoff"][str(int(cutoff))])
    radial_low = float(metrics["radial_effective_scale"]) <= float(r0) and high_tail < float(eta)
    if radial_low:
        return "low-radial-band"
    radial_shell_max = metrics.get("radial_shell_max")
    if high_tail < float(eta) and isinstance(radial_shell_max, (int, float)) and float(radial_shell_max) < float(cutoff):
        return "finite-low-shell-degeneracy"
    if isinstance(worst_shell, (int, float)) and int(worst_shell) <= int(finite_shell_cutoff):
        return "finite-low-shell-degeneracy"
    if high_tail >= float(eta):
        if not isinstance(worst_shell, (int, float)):
            return "partial"
        return "asymptotic-tail-danger"
    return "partial"


def _tail_grid(
    *,
    lambda_min: Any,
    metrics: dict[str, Any],
    worst_shell: Any,
    c0_values: list[float],
    r0: float,
    tail_cutoffs: list[int],
    tail_etas: list[float],
    d0_values: list[float],
    finite_shell_cutoff: int,
) -> list[dict[str, Any]]:
    grid: list[dict[str, Any]] = []
    for c0 in c0_values:
        for cutoff in tail_cutoffs:
            for eta in tail_etas:
                for d0 in d0_values:
                    grid.append(
                        {
                            "c0": float(c0),
                            "tail_cutoff": int(cutoff),
                            "tail_eta": float(eta),
                            "d0": float(d0),
                            "high_shell_mass_k": float(metrics["high_shell_mass_by_cutoff"][str(int(cutoff))]),
                            "branch": _classify_tail(
                                lambda_min=lambda_min,
                                metrics=metrics,
                                worst_shell=worst_shell,
                                c0=float(c0),
                                r0=float(r0),
                                cutoff=int(cutoff),
                                eta=float(eta),
                                d0=float(d0),
                                finite_shell_cutoff=int(finite_shell_cutoff),
                            ),
                        }
                    )
    return grid


def _summarize_grid(grid: list[dict[str, Any]]) -> dict[str, Any]:
    counts: dict[str, int] = {}
    for item in grid:
        branch = str(item.get("branch"))
        counts[branch] = counts.get(branch, 0) + 1
    return {
        "grid_point_count": int(len(grid)),
        "branch_counts": counts,
        "asymptotic_tail_danger_count": int(counts.get("asymptotic-tail-danger", 0)),
        "finite_low_shell_degeneracy_count": int(counts.get("finite-low-shell-degeneracy", 0)),
        "high_dissipation_count": int(counts.get("high-dissipation", 0)),
        "frame_coercive_count": int(counts.get("frame-coercive", 0)),
    }


def _metrics_for_all_cutoffs(
    probability: np.ndarray,
    shell_levels: np.ndarray,
    zero_eps: float,
    tail_cutoffs: list[int],
    eta_values: list[float],
) -> dict[str, Any]:
    base = _profile_metrics(probability, shell_levels, zero_eps, min(tail_cutoffs))
    base["high_shell_mass_by_cutoff"] = {
        str(int(cutoff)): _tail_mass(shell_levels, probability, int(cutoff)) for cutoff in tail_cutoffs
    }
    base["radial_shell_max_with_mass_eta"] = {
        f"{float(eta):.6g}": _radial_max_with_mass_eta(shell_levels, probability, float(eta))
        for eta in eta_values
    }
    return base


def _forced_tail_profiles(
    shell_levels: np.ndarray,
    tail_cutoffs: list[int],
    tail_etas: list[float],
    zero_eps: float,
) -> list[tuple[str, np.ndarray]]:
    profiles: list[tuple[str, np.ndarray]] = []
    shells = np.asarray(shell_levels, dtype=np.float64)
    low_shell = float(np.min(shells))
    low_mask = shells <= low_shell + 1.0e-12
    if not np.any(low_mask):
        return profiles
    low_reference = _normalize_profile(np.where(low_mask, 1.0, 0.0), zero_eps)
    for cutoff in tail_cutoffs:
        high_mask = shells >= float(cutoff)
        if not np.any(high_mask):
            continue
        high_reference = _normalize_profile(np.where(high_mask, 1.0, 0.0), zero_eps)
        for eta in tail_etas:
            eta_value = min(max(float(eta), 0.0), 1.0)
            probability = _normalize_profile(
                (1.0 - eta_value) * low_reference + eta_value * high_reference,
                zero_eps,
            )
            profiles.append((f"forced_tail_K{int(cutoff)}_eta_{eta_value:.3f}", probability))
    return profiles


def _row(
    *,
    slot: int,
    snapshot: int,
    bundle: Any,
    shell_n: int,
    backend: str,
    zero_eps: float,
    sample_count: int,
    mix_count: int,
    seeds: list[int],
    c0_values: list[float],
    r0: float,
    tail_cutoffs: list[int],
    tail_etas: list[float],
    d0_values: list[float],
    parity_tol: float,
    lobpcg_tol: float,
    lobpcg_maxiter: int,
    block_size: int,
    generalized_mass_shift: float,
    dense_oracle_shell_limit: int,
    gpu_checks: int,
    max_profiles_per_row: int,
    profile_sample_limit: int,
    finite_shell_cutoff: int,
    force_tail_profiles: bool,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "shell": int(shell_n),
        "kn_backend": backend,
        "candidate_only": True,
        "fail_closed": True,
        "gpu_kn_authority": False,
        "dense_reconstruction_used": False,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        shell_modes = _cube_modes(spectrum, shell_n=shell_n, zero_eps=zero_eps)
        triads, frame_metrics = _build_frame_surface(shell_modes, zero_eps=zero_eps, triad_sample_limit=8)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"tail_progression_scan_error: {exc}"]
        return row

    row["selected_mode_count"] = int(len(shell_modes))
    row["triad_count"] = int(len(triads))
    row["carrier_stratum_count"] = int(frame_metrics.get("carrier_stratum_count", 0))
    row["dense_oracle_used"] = bool(int(shell_n) <= int(dense_oracle_shell_limit))
    if len(shell_modes) < 3 or not triads:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_insufficient_modes"]
        row["profile_count"] = 0
        return row

    amplitudes = np.asarray([float(mode.amplitude) for mode in shell_modes], dtype=np.float64)
    base_probability = _normalize_profile(amplitudes * amplitudes, zero_eps)
    shell_radii = np.asarray([float(mode.shell_radius) for mode in shell_modes], dtype=np.float64)
    levels = _shell_levels(shell_radii)

    evaluated: list[dict[str, Any]] = []
    seen: set[str] = set()
    profile_queue: list[tuple[str, np.ndarray]] = []
    if force_tail_profiles:
        profile_queue.extend(_forced_tail_profiles(levels, tail_cutoffs, tail_etas, zero_eps))
    for seed in seeds:
        profile_queue.extend(
            (f"seed{seed}:{profile_id}", probability)
            for profile_id, probability in _candidate_profiles(base_probability, levels, sample_count, mix_count, seed, zero_eps)
        )

    for unique_id, probability in profile_queue:
        if int(max_profiles_per_row) > 0 and len(evaluated) >= int(max_profiles_per_row):
            break
        if unique_id in seen:
            continue
        seen.add(unique_id)
        solved = _evaluate(
            triads=triads,
            probability=probability,
            shell_levels=levels,
            profile_id=unique_id,
            shell_n=shell_n,
            backend=backend,
            zero_eps=zero_eps,
            high_shell_cutoff=float(min(tail_cutoffs)),
            r0=r0,
            high_shell_eta=min(tail_etas),
            d0=max(d0_values),
            parity_tol=parity_tol,
            lobpcg_tol=lobpcg_tol,
            lobpcg_maxiter=lobpcg_maxiter,
            block_size=block_size,
            generalized_mass_shift=generalized_mass_shift,
            dense_oracle_shell_limit=dense_oracle_shell_limit,
            gpu_checks=gpu_checks,
        )
        metrics = _metrics_for_all_cutoffs(probability, levels, zero_eps, tail_cutoffs, tail_etas)
        tail_grid = _tail_grid(
            lambda_min=solved.get("lambda_min_iterative"),
            metrics=metrics,
            worst_shell=solved.get("worst_eigenvector_shell_iterative"),
            c0_values=c0_values,
            r0=r0,
            tail_cutoffs=tail_cutoffs,
            tail_etas=tail_etas,
            d0_values=d0_values,
            finite_shell_cutoff=finite_shell_cutoff,
        )
        evaluated.append(
            {
                "profile_id": unique_id,
                "status": solved.get("status"),
                "parity_ok": solved.get("parity_ok"),
                "candidate_only": True,
                "fail_closed": True,
                "kn_backend": backend,
                "gpu_kn_authority": False,
                "dense_oracle_used": solved.get("dense_oracle_used"),
                "dense_reconstruction_used": False,
                "lambda_min_dense_cpu": solved.get("lambda_min_dense_cpu"),
                "lambda_min_iterative": solved.get("lambda_min_iterative"),
                "relative_error_vs_dense": solved.get("relative_error_vs_dense"),
                "worst_eigenvector_shell_iterative": solved.get("worst_eigenvector_shell_iterative"),
                "worst_eigenvector_shell_mass_iterative": solved.get("worst_eigenvector_shell_mass_iterative"),
                "iterations": solved.get("iterations"),
                "residual_norm": solved.get("residual_norm"),
                "elapsed_ms": solved.get("elapsed_ms"),
                "block_matvec_enabled": solved.get("block_matvec_enabled"),
                "block_matvec_backend": solved.get("block_matvec_backend"),
                "gpu_matvec_parity_ok": solved.get("gpu_matvec_parity_ok"),
                "gpu_block_matvec_parity_ok": solved.get("gpu_block_matvec_parity_ok"),
                "vulkan_icd": solved.get("vulkan_icd"),
                "metrics": metrics,
                "tail_grid_summary": _summarize_grid(tail_grid),
                "tail_grid": tail_grid,
                "warnings": solved.get("warnings", []),
            }
        )

    best = min(
        (item for item in evaluated if isinstance(item.get("lambda_min_iterative"), (int, float))),
        key=lambda item: float(item["lambda_min_iterative"]),
        default=None,
    )
    asymptotic_candidates = [
        item
        for item in evaluated
        if int(item["tail_grid_summary"].get("asymptotic_tail_danger_count", 0)) > 0
    ]
    row.update(
        {
            "status": OK_STATUS if evaluated and all(item.get("parity_ok") is True for item in evaluated) else PARTIAL_STATUS,
            "profile_count": int(len(evaluated)),
            "parity_ok_count": int(sum(1 for item in evaluated if item.get("parity_ok") is True)),
            "parity_mismatch_count": int(sum(1 for item in evaluated if item.get("parity_ok") is not True)),
            "asymptotic_tail_candidate_count": int(len(asymptotic_candidates)),
            "best_profile": best,
            "profile_samples": evaluated[: min(max(0, int(profile_sample_limit)), len(evaluated))],
        }
    )
    return row


def _aggregate(rows: list[dict[str, Any]], backend: str) -> dict[str, Any]:
    total_profiles = sum(int(row.get("profile_count", 0)) for row in rows)
    parity_mismatches = sum(int(row.get("parity_mismatch_count", 0)) for row in rows)
    asymptotic_candidates = sum(int(row.get("asymptotic_tail_candidate_count", 0)) for row in rows)
    best_profiles = [
        row.get("best_profile")
        for row in rows
        if isinstance(row.get("best_profile"), dict)
        and isinstance(row.get("best_profile", {}).get("lambda_min_iterative"), (int, float))
    ]
    best_global = min(best_profiles, key=lambda item: float(item["lambda_min_iterative"])) if best_profiles else None
    worst_shells = [
        int(profile["worst_eigenvector_shell_iterative"])
        for profile in best_profiles
        if isinstance(profile.get("worst_eigenvector_shell_iterative"), (int, float))
    ]
    return {
        "processed_rows": int(len(rows)),
        "ok_rows": int(sum(1 for row in rows if row.get("status") == OK_STATUS)),
        "partial_rows": int(sum(1 for row in rows if row.get("status") == PARTIAL_STATUS)),
        "error_rows": int(sum(1 for row in rows if row.get("status") == ERROR_STATUS)),
        "kn_backend": backend,
        "sampled_profile_count": int(total_profiles),
        "parity_mismatch_count": int(parity_mismatches),
        "asymptotic_tail_candidate_count": int(asymptotic_candidates),
        "best_global_profile": best_global,
        "best_profile_worst_shells": worst_shells,
        "worst_shell_progression_max": max(worst_shells) if worst_shells else None,
        "candidate_only": True,
        "fail_closed": True,
        "gpu_kn_authority": False,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "dense_eigensolve_scope": "small_shell_oracle_only",
        "dense_reconstruction_used_by_iterative_lane": False,
        "tail_progression_status": "fail-closed" if parity_mismatches else "candidate-tail-telemetry",
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells if args.shells is not None else list(DEFAULT_SHELLS))
    seeds = [int(seed) for seed in (args.seeds if args.seeds is not None else list(DEFAULT_SEEDS))]
    c0_values = [float(value) for value in args.c0_values]
    tail_cutoffs = sorted({int(value) for value in args.tail_cutoffs})
    tail_etas = [float(value) for value in args.tail_etas]
    d0_values = [float(value) for value in args.d0_values]
    warnings: list[str] = []
    if args.kn_backend == "vulkan-matvec":
        warnings.append("vulkan_matvec_backend_non_authoritative_gpu_kn_authority_false")
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    snapshots = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)
    rows = [
        _row(
            slot=slot,
            snapshot=snapshot,
            bundle=bundle,
            shell_n=shell_n,
            backend=args.kn_backend,
            zero_eps=float(args.zero_eps),
            sample_count=int(args.sample_count),
            mix_count=int(args.mix_count),
            seeds=seeds,
            c0_values=c0_values,
            r0=float(args.r0),
            tail_cutoffs=tail_cutoffs,
            tail_etas=tail_etas,
            d0_values=d0_values,
            parity_tol=float(args.parity_tol),
            lobpcg_tol=float(args.lobpcg_tol),
            lobpcg_maxiter=int(args.lobpcg_maxiter),
            block_size=int(args.block_size),
            generalized_mass_shift=float(args.generalized_mass_shift),
            dense_oracle_shell_limit=int(args.dense_oracle_shell_limit),
            gpu_checks=int(args.gpu_matvec_checks),
            max_profiles_per_row=int(args.max_profiles_per_row),
            profile_sample_limit=int(args.profile_sample_limit),
            finite_shell_cutoff=int(args.finite_shell_cutoff),
            force_tail_profiles=not bool(args.no_force_tail_profiles),
        )
        for slot, snapshot in enumerate(snapshots)
        for shell_n in shells
    ]
    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "parameters": {
            "raw_archive": str(args.raw_archive),
            "output_json": str(args.output_json),
            "kn_backend": args.kn_backend,
            "frame": args.frame,
            "frame_limit": int(args.frame_limit),
            "zero_eps": float(args.zero_eps),
            "sample_count": int(args.sample_count),
            "mix_count": int(args.mix_count),
            "max_profiles_per_row": int(args.max_profiles_per_row),
            "profile_sample_limit": int(args.profile_sample_limit),
            "seeds": seeds,
            "shells": [int(shell) for shell in shells],
            "c0_values": c0_values,
            "r0": float(args.r0),
            "tail_cutoffs": tail_cutoffs,
            "tail_etas": tail_etas,
            "d0_values": d0_values,
            "finite_shell_cutoff": int(args.finite_shell_cutoff),
            "force_tail_profiles": not bool(args.no_force_tail_profiles),
            "parity_tol": float(args.parity_tol),
            "lobpcg_tol": float(args.lobpcg_tol),
            "lobpcg_maxiter": int(args.lobpcg_maxiter),
            "block_size": int(args.block_size),
            "generalized_mass_shift": float(args.generalized_mass_shift),
            "dense_oracle_shell_limit": int(args.dense_oracle_shell_limit),
            "gpu_matvec_checks": int(args.gpu_matvec_checks),
        },
        "status": ERROR_STATUS if any(row.get("status") == ERROR_STATUS for row in rows) else (
            OK_STATUS if rows and all(row.get("status") == OK_STATUS for row in rows) else PARTIAL_STATUS
        ),
        "rows": rows,
        "aggregate": _aggregate(rows, args.kn_backend),
        "warnings": warnings,
        "errors": [error for row in rows for error in row.get("errors", [])],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if payload["status"] != ERROR_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
