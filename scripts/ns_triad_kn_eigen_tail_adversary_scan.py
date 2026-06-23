#!/usr/bin/env python3
"""Focused adversary scan for matrix-free NS triad K_N(A) eigen tails.

This harness reuses the existing candidate profile generator together with the
iterative generalized-eigen evaluation lane. It deliberately biases toward
high tail mass, ranks low-lambda candidates, and classifies whether the
worst eigenvector escapes into the high-shell region. The scan is candidate-
only and fail-closed: gpu_kn_authority, theorem_promoted, full_ns_promoted,
and clay_promoted stay false throughout.
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
from ns_triad_kn_tail_progression_scan import _eigen_shell_telemetry  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_eigen_tail_adversary_scan.py"
CONTRACT = "ns_triad_kn_eigen_tail_adversary_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EIGEN_TAIL_ADVERSARY_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_eigen_tail_adversary_scan_N128_20260623.json"
)
DEFAULT_SHELLS = (4, 5)
DEFAULT_SAMPLE_COUNT = 4
DEFAULT_MIX_COUNT = 2
DEFAULT_SEEDS = (0,)
DEFAULT_C0_VALUES = (0.10, 0.25)
DEFAULT_TAIL_CUTOFFS = (4, 5, 6)
DEFAULT_TAIL_ETAS = (0.25, 0.40)
DEFAULT_PROFILE_SAMPLE_LIMIT = 6
DEFAULT_MAX_PROFILES_PER_ROW = 4
TAIL_GRID_DETAIL_CHOICES = ("full", "summary", "none")
DEFAULT_PARITY_TOL = 1.0e-4
DEFAULT_LOBPCG_TOL = 1.0e-5
DEFAULT_LOBPCG_MAXITER = 40
DEFAULT_GENERALIZED_MASS_SHIFT = 1.0e-8
DEFAULT_DENSE_ORACLE_SHELL_LIMIT = 3
DEFAULT_GPU_MATVEC_CHECKS = 1

CONTROL_CARD = {
    "O": "Run a focused adversary scan that pushes K_N(A) profile tails upward and ranks the low-lambda survivors.",
    "R": (
        "Use the existing candidate-profile generator and iterative generalized eigen evaluator, "
        "bias profiles toward high-shell mass, and classify whether the worst eigenvector escapes "
        "into the tail region."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; no theorem, full-NS, or Clay promotion is inferred.",
    "L": (
        "Load shell carriers, build tail-biased amplitude profiles, solve L_neg x = lambda L_abs x "
        "with CPU or Vulkan matvecs, and report the lowest lambda candidates together with tail-escape labels."
    ),
    "P": ROUTE_DECISION,
    "G": "GPU matvecs remain non-authoritative and gpu_kn_authority is always false.",
    "F": "This is a focused empirical adversary scan; it does not prove any asymptotic tail exclusion.",
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
    parser.add_argument("--seed", dest="seeds", action="append", type=int, default=None)
    parser.add_argument("--c0-values", type=lambda text: _parse_csv_numbers(text, float), default=list(DEFAULT_C0_VALUES))
    parser.add_argument("--tail-cutoffs", type=lambda text: _parse_csv_numbers(text, int), default=list(DEFAULT_TAIL_CUTOFFS))
    parser.add_argument("--tail-etas", type=lambda text: _parse_csv_numbers(text, float), default=list(DEFAULT_TAIL_ETAS))
    parser.add_argument("--r0", type=float, default=DEFAULT_R0)
    parser.add_argument("--d0", type=float, default=DEFAULT_D0)
    parser.add_argument("--parity-tol", type=float, default=DEFAULT_PARITY_TOL)
    parser.add_argument("--lobpcg-tol", type=float, default=DEFAULT_LOBPCG_TOL)
    parser.add_argument("--lobpcg-maxiter", type=int, default=DEFAULT_LOBPCG_MAXITER)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--generalized-mass-shift", type=float, default=DEFAULT_GENERALIZED_MASS_SHIFT)
    parser.add_argument("--dense-oracle-shell-limit", type=int, default=DEFAULT_DENSE_ORACLE_SHELL_LIMIT)
    parser.add_argument("--gpu-matvec-checks", type=int, default=DEFAULT_GPU_MATVEC_CHECKS)
    parser.add_argument("--profile-sample-limit", type=int, default=DEFAULT_PROFILE_SAMPLE_LIMIT)
    parser.add_argument("--max-profiles-per-row", type=int, default=DEFAULT_MAX_PROFILES_PER_ROW)
    parser.add_argument(
        "--tail-grid-detail",
        choices=TAIL_GRID_DETAIL_CHOICES,
        default="full",
        help="control how much tail-grid detail is serialized per profile",
    )
    parser.add_argument("--force-tail-profiles", action="store_true", default=True)
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


def _classify_tail_escape(
    *,
    lambda_min: Any,
    metrics: dict[str, Any],
    worst_shell: Any,
    cutoff: int,
    eta: float,
    c0: float,
) -> str:
    if not isinstance(lambda_min, (int, float)) or not math.isfinite(float(lambda_min)):
        return "unavailable"
    if float(lambda_min) >= float(c0):
        return "frame-coercive"

    high_tail = float(metrics["high_shell_mass_by_cutoff"][str(int(cutoff))])
    eigen_tail_map = metrics.get("eigen_tail_mass_by_cutoff")
    eigen_tail_mass = (
        eigen_tail_map.get(str(int(cutoff)))
        if isinstance(eigen_tail_map, dict)
        else None
    )
    worst_shell_value = int(worst_shell) if isinstance(worst_shell, (int, float)) else None
    shell_escape = worst_shell_value is not None and worst_shell_value >= int(cutoff)
    eigen_tail_escape = (
        float(eigen_tail_mass) >= float(eta)
        if isinstance(eigen_tail_mass, (int, float)) and math.isfinite(float(eigen_tail_mass))
        else shell_escape
    )

    if high_tail >= float(eta) and eigen_tail_escape:
        return "tail-escape"
    if high_tail >= float(eta):
        return "tail-loaded"
    if eigen_tail_escape:
        return "eigenvector-tail-escape"
    return "tail-contained"


def _tail_grid(
    *,
    lambda_min: Any,
    metrics: dict[str, Any],
    worst_shell: Any,
    c0_values: list[float],
    tail_cutoffs: list[int],
    tail_etas: list[float],
) -> list[dict[str, Any]]:
    grid: list[dict[str, Any]] = []
    eigen_tail_map = metrics.get("eigen_tail_mass_by_cutoff")
    for c0 in c0_values:
        for cutoff in tail_cutoffs:
            for eta in tail_etas:
                eigen_tail_mass = (
                    eigen_tail_map.get(str(int(cutoff)))
                    if isinstance(eigen_tail_map, dict)
                    else None
                )
                grid.append(
                    {
                        "c0": float(c0),
                        "tail_cutoff": int(cutoff),
                        "tail_eta": float(eta),
                        "high_shell_mass_k": float(metrics["high_shell_mass_by_cutoff"][str(int(cutoff))]),
                        "eigen_tail_mass_k": (
                            float(eigen_tail_mass)
                            if isinstance(eigen_tail_mass, (int, float)) and math.isfinite(float(eigen_tail_mass))
                            else None
                        ),
                        "eigen_tail_high": (
                            bool(float(eigen_tail_mass) >= float(eta))
                            if isinstance(eigen_tail_mass, (int, float)) and math.isfinite(float(eigen_tail_mass))
                            else None
                        ),
                        "branch": _classify_tail_escape(
                            lambda_min=lambda_min,
                            metrics=metrics,
                            worst_shell=worst_shell,
                            cutoff=int(cutoff),
                            eta=float(eta),
                            c0=float(c0),
                        ),
                    }
                )
    return grid


def _summarize_grid(grid: list[dict[str, Any]]) -> dict[str, Any]:
    counts: dict[str, int] = {}
    profile_tail_high_count = 0
    profile_tail_high_eigen_tail_high_count = 0
    profile_tail_high_eigen_tail_low_count = 0
    profile_tail_high_eigen_tail_unavailable_count = 0
    for item in grid:
        branch = str(item.get("branch"))
        counts[branch] = counts.get(branch, 0) + 1
        high_shell_mass = item.get("high_shell_mass_k")
        tail_eta = item.get("tail_eta")
        profile_tail_high = (
            isinstance(high_shell_mass, (int, float))
            and math.isfinite(float(high_shell_mass))
            and isinstance(tail_eta, (int, float))
            and math.isfinite(float(tail_eta))
            and float(high_shell_mass) >= float(tail_eta)
        )
        if profile_tail_high:
            profile_tail_high_count += 1
            eigen_tail_high = item.get("eigen_tail_high")
            if eigen_tail_high is True:
                profile_tail_high_eigen_tail_high_count += 1
            elif eigen_tail_high is False:
                profile_tail_high_eigen_tail_low_count += 1
            else:
                profile_tail_high_eigen_tail_unavailable_count += 1
    return {
        "grid_point_count": int(len(grid)),
        "branch_counts": counts,
        "tail_escape_count": int(counts.get("tail-escape", 0)),
        "eigenvector_tail_escape_count": int(counts.get("eigenvector-tail-escape", 0)),
        "tail_loaded_count": int(counts.get("tail-loaded", 0)),
        "tail_contained_count": int(counts.get("tail-contained", 0)),
        "frame_coercive_count": int(counts.get("frame-coercive", 0)),
        "profile_tail_high_count": int(profile_tail_high_count),
        "profile_tail_high_eigen_tail_high_count": int(profile_tail_high_eigen_tail_high_count),
        "profile_tail_high_eigen_tail_low_count": int(profile_tail_high_eigen_tail_low_count),
        "profile_tail_high_eigen_tail_unavailable_count": int(profile_tail_high_eigen_tail_unavailable_count),
    }


def _metrics_for_all_cutoffs(
    probability: np.ndarray,
    shell_levels: np.ndarray,
    zero_eps: float,
    tail_cutoffs: list[int],
    eta_values: list[float],
    eigen_telemetry: dict[str, Any] | None = None,
) -> dict[str, Any]:
    base = _profile_metrics(probability, shell_levels, zero_eps, min(tail_cutoffs))
    base["high_shell_mass_by_cutoff"] = {
        str(int(cutoff)): _tail_mass(shell_levels, probability, int(cutoff)) for cutoff in tail_cutoffs
    }
    base["radial_shell_max_with_mass_eta"] = {
        f"{float(eta):.6g}": _radial_max_with_mass_eta(shell_levels, probability, float(eta))
        for eta in eta_values
    }
    if eigen_telemetry is not None:
        base.update(eigen_telemetry)
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
    tail_cutoffs: list[int],
    tail_etas: list[float],
    r0: float,
    d0: float,
    parity_tol: float,
    lobpcg_tol: float,
    lobpcg_maxiter: int,
    block_size: int,
    generalized_mass_shift: float,
    dense_oracle_shell_limit: int,
    gpu_checks: int,
    max_profiles_per_row: int,
    profile_sample_limit: int,
    tail_grid_detail: str,
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
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "dense_reconstruction_used": False,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        shell_modes = _cube_modes(spectrum, shell_n=shell_n, zero_eps=zero_eps)
        triads, frame_metrics = _build_frame_surface(shell_modes, zero_eps=zero_eps, triad_sample_limit=8)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"eigen_tail_adversary_scan_error: {exc}"]
        return row

    row["selected_mode_count"] = int(len(shell_modes))
    row["triad_count"] = int(len(triads))
    row["carrier_stratum_count"] = int(frame_metrics.get("carrier_stratum_count", 0))
    row["dense_oracle_used"] = bool(int(shell_n) <= int(dense_oracle_shell_limit))
    row["tail_biased_scan"] = True
    if int(shell_n) >= 4:
        row["dense_reconstruction_used"] = False
    if len(shell_modes) < 3 or not triads:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_insufficient_modes"]
        row["profile_count"] = 0
        row["candidate_receipt_count"] = 0
        row["tail_grid_point_count"] = 0
        row["tail_escape_count"] = 0
        row["eigenvector_tail_escape_count"] = 0
        row["tail_loaded_count"] = 0
        row["tail_contained_count"] = 0
        row["frame_coercive_count"] = 0
        row["profile_tail_high_count"] = 0
        row["profile_tail_high_eigen_tail_high_count"] = 0
        row["profile_tail_high_eigen_tail_low_count"] = 0
        row["profile_tail_high_eigen_tail_unavailable_count"] = 0
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
            d0=d0,
            parity_tol=parity_tol,
            lobpcg_tol=lobpcg_tol,
            lobpcg_maxiter=lobpcg_maxiter,
            block_size=block_size,
            generalized_mass_shift=generalized_mass_shift,
            dense_oracle_shell_limit=dense_oracle_shell_limit,
            gpu_checks=gpu_checks,
        )
        row_warnings = list(solved.get("warnings", []) or [])
        try:
            eigen_telemetry = _eigen_shell_telemetry(
                triads=triads,
                probability=probability,
                shell_levels=levels,
                profile_id=unique_id,
                backend=backend,
                zero_eps=zero_eps,
                tail_cutoffs=tail_cutoffs,
                tail_etas=tail_etas,
                lobpcg_tol=lobpcg_tol,
                lobpcg_maxiter=lobpcg_maxiter,
                block_size=block_size,
                generalized_mass_shift=generalized_mass_shift,
                gpu_checks=gpu_checks,
            )
        except Exception as exc:  # noqa: BLE001
            eigen_telemetry = {
                "eigen_tail_mass_by_cutoff": {str(int(cutoff)): None for cutoff in tail_cutoffs},
                "eigen_shell_barycenter": None,
                "eigen_shell_variance": None,
                "eigen_shell_max_with_mass_eta": {f"{float(eta):.6g}": None for eta in tail_etas},
            }
            row_warnings.append(f"eigen_tail_telemetry_error: {type(exc).__name__}: {exc}")
        metrics = _metrics_for_all_cutoffs(probability, levels, zero_eps, tail_cutoffs, tail_etas, eigen_telemetry)
        tail_grid = _tail_grid(
            lambda_min=solved.get("lambda_min_iterative"),
            metrics=metrics,
            worst_shell=solved.get("worst_eigenvector_shell_iterative"),
            c0_values=c0_values,
            tail_cutoffs=tail_cutoffs,
            tail_etas=tail_etas,
        )
        lmin = solved.get("lambda_min_iterative")
        lambda_rank = (
            float(lmin)
            if isinstance(lmin, (int, float)) and math.isfinite(float(lmin))
            else None
        )
        tail_grid_summary = _summarize_grid(tail_grid)
        tail_grid_counts = {
            "tail_grid_point_count": int(tail_grid_summary.get("grid_point_count", 0)),
            "tail_escape_count": int(tail_grid_summary.get("tail_escape_count", 0)),
            "eigenvector_tail_escape_count": int(tail_grid_summary.get("eigenvector_tail_escape_count", 0)),
            "tail_loaded_count": int(tail_grid_summary.get("tail_loaded_count", 0)),
            "tail_contained_count": int(tail_grid_summary.get("tail_contained_count", 0)),
            "frame_coercive_count": int(tail_grid_summary.get("frame_coercive_count", 0)),
            "profile_tail_high_count": int(tail_grid_summary.get("profile_tail_high_count", 0)),
            "profile_tail_high_eigen_tail_high_count": int(
                tail_grid_summary.get("profile_tail_high_eigen_tail_high_count", 0)
            ),
            "profile_tail_high_eigen_tail_low_count": int(
                tail_grid_summary.get("profile_tail_high_eigen_tail_low_count", 0)
            ),
            "profile_tail_high_eigen_tail_unavailable_count": int(
                tail_grid_summary.get("profile_tail_high_eigen_tail_unavailable_count", 0)
            ),
        }
        row_payload: dict[str, Any] = {
            "profile_id": unique_id,
            "status": solved.get("status"),
            "parity_ok": solved.get("parity_ok"),
            "candidate_only": True,
            "fail_closed": True,
            "kn_backend": backend,
            "gpu_kn_authority": False,
            "theorem_promoted": False,
            "full_ns_promoted": False,
            "clay_promoted": False,
            "dense_oracle_used": solved.get("dense_oracle_used"),
            "dense_reconstruction_used": False,
            "lambda_min_dense_cpu": solved.get("lambda_min_dense_cpu"),
            "lambda_min_iterative": lmin,
            "lambda_rank": lambda_rank,
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
            "gpu_matvec_max_abs_error_abs": solved.get("gpu_matvec_max_abs_error_abs"),
            "gpu_matvec_max_abs_error_neg": solved.get("gpu_matvec_max_abs_error_neg"),
            "vulkan_icd": solved.get("vulkan_icd"),
            "metrics": metrics,
            **tail_grid_counts,
            "tail_grid_detail": {
                "mode": tail_grid_detail,
                "summary": tail_grid_summary if tail_grid_detail == "summary" else None,
            },
            "warnings": row_warnings,
        }
        if tail_grid_detail in {"full", "summary"}:
            row_payload["tail_grid_summary"] = tail_grid_summary
        if tail_grid_detail == "full":
            row_payload["tail_grid"] = tail_grid
        evaluated.append(
            row_payload
        )

    evaluated.sort(
        key=lambda item: (
            float("inf")
            if not isinstance(item.get("lambda_min_iterative"), (int, float))
            else float(item["lambda_min_iterative"]),
            -int(item.get("tail_escape_count", 0)),
        )
    )
    best = evaluated[0] if evaluated else None
    tail_escape_candidates = [
        item for item in evaluated if int(item.get("tail_escape_count", 0)) > 0
    ]
    row.update(
        {
            "status": OK_STATUS if evaluated and all(item.get("parity_ok") is True for item in evaluated) else PARTIAL_STATUS,
            "profile_count": int(len(evaluated)),
            "candidate_receipt_count": int(len(evaluated)),
            "parity_ok_count": int(sum(1 for item in evaluated if item.get("parity_ok") is True)),
            "parity_mismatch_count": int(sum(1 for item in evaluated if item.get("parity_ok") is not True)),
            "tail_escape_candidate_count": int(len(tail_escape_candidates)),
            "tail_grid_point_count": int(sum(int(item.get("tail_grid_point_count", 0)) for item in evaluated)),
            "tail_escape_count": int(sum(int(item.get("tail_escape_count", 0)) for item in evaluated)),
            "eigenvector_tail_escape_count": int(
                sum(int(item.get("eigenvector_tail_escape_count", 0)) for item in evaluated)
            ),
            "tail_loaded_count": int(sum(int(item.get("tail_loaded_count", 0)) for item in evaluated)),
            "tail_contained_count": int(sum(int(item.get("tail_contained_count", 0)) for item in evaluated)),
            "frame_coercive_count": int(sum(int(item.get("frame_coercive_count", 0)) for item in evaluated)),
            "profile_tail_high_count": int(sum(int(item.get("profile_tail_high_count", 0)) for item in evaluated)),
            "profile_tail_high_eigen_tail_high_count": int(
                sum(int(item.get("profile_tail_high_eigen_tail_high_count", 0)) for item in evaluated)
            ),
            "profile_tail_high_eigen_tail_low_count": int(
                sum(int(item.get("profile_tail_high_eigen_tail_low_count", 0)) for item in evaluated)
            ),
            "profile_tail_high_eigen_tail_unavailable_count": int(
                sum(int(item.get("profile_tail_high_eigen_tail_unavailable_count", 0)) for item in evaluated)
            ),
            "best_low_lambda_profile": best,
            "best_tail_escape_profile": min(
                tail_escape_candidates,
                key=lambda item: float(item["lambda_min_iterative"])
                if isinstance(item.get("lambda_min_iterative"), (int, float))
                else float("inf"),
                default=None,
            ),
            "best_low_lambda_rows": [
                {
                    "frame": int(slot),
                    "snapshot_index": int(snapshot),
                    "shell": int(shell_n),
                    "profile_id": item.get("profile_id"),
                    "lambda_min_iterative": (
                        float(item["lambda_min_iterative"])
                        if isinstance(item.get("lambda_min_iterative"), (int, float))
                        else None
                    ),
                    "tail_escape_count": int(item.get("tail_escape_count", 0)),
                    "tail_escape_candidate": bool(int(item.get("tail_escape_count", 0)) > 0),
                    "worst_eigenvector_shell_iterative": (
                        float(item["worst_eigenvector_shell_iterative"])
                        if isinstance(item.get("worst_eigenvector_shell_iterative"), (int, float))
                        else None
                    ),
                    "worst_eigenvector_shell_mass_iterative": (
                        float(item["worst_eigenvector_shell_mass_iterative"])
                        if isinstance(item.get("worst_eigenvector_shell_mass_iterative"), (int, float))
                        else None
                    ),
                }
                for item in evaluated[: min(5, len(evaluated))]
            ],
            "candidate_receipts": evaluated[: min(max(0, int(profile_sample_limit)), len(evaluated))],
        }
    )
    return row


def _aggregate(rows: list[dict[str, Any]], backend: str) -> dict[str, Any]:
    total_candidates = sum(int(row.get("candidate_receipt_count", 0)) for row in rows)
    parity_mismatches = sum(int(row.get("parity_mismatch_count", 0)) for row in rows)
    tail_escape_candidates = sum(int(row.get("tail_escape_candidate_count", 0)) for row in rows)
    tail_grid_point_count = sum(int(row.get("tail_grid_point_count", 0)) for row in rows)
    tail_escape_count = sum(int(row.get("tail_escape_count", 0)) for row in rows)
    eigenvector_tail_escape_count = sum(int(row.get("eigenvector_tail_escape_count", 0)) for row in rows)
    tail_loaded_count = sum(int(row.get("tail_loaded_count", 0)) for row in rows)
    tail_contained_count = sum(int(row.get("tail_contained_count", 0)) for row in rows)
    frame_coercive_count = sum(int(row.get("frame_coercive_count", 0)) for row in rows)
    profile_tail_high_count = sum(int(row.get("profile_tail_high_count", 0)) for row in rows)
    profile_tail_high_eigen_tail_high_count = sum(
        int(row.get("profile_tail_high_eigen_tail_high_count", 0)) for row in rows
    )
    profile_tail_high_eigen_tail_low_count = sum(
        int(row.get("profile_tail_high_eigen_tail_low_count", 0)) for row in rows
    )
    profile_tail_high_eigen_tail_unavailable_count = sum(
        int(row.get("profile_tail_high_eigen_tail_unavailable_count", 0)) for row in rows
    )
    best_profiles = [
        row.get("best_low_lambda_profile")
        for row in rows
        if isinstance(row.get("best_low_lambda_profile"), dict)
        and isinstance(row.get("best_low_lambda_profile", {}).get("lambda_min_iterative"), (int, float))
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
        "candidate_receipt_count": int(total_candidates),
        "parity_mismatch_count": int(parity_mismatches),
        "tail_escape_candidate_count": int(tail_escape_candidates),
        "tail_grid_point_count": int(tail_grid_point_count),
        "tail_escape_count": int(tail_escape_count),
        "eigenvector_tail_escape_count": int(eigenvector_tail_escape_count),
        "tail_loaded_count": int(tail_loaded_count),
        "tail_contained_count": int(tail_contained_count),
        "frame_coercive_count": int(frame_coercive_count),
        "profile_tail_high_count": int(profile_tail_high_count),
        "profile_tail_high_eigen_tail_high_count": int(profile_tail_high_eigen_tail_high_count),
        "profile_tail_high_eigen_tail_low_count": int(profile_tail_high_eigen_tail_low_count),
        "profile_tail_high_eigen_tail_unavailable_count": int(profile_tail_high_eigen_tail_unavailable_count),
        "best_global_low_lambda_profile": best_global,
        "best_global_low_lambda": (
            float(best_global["lambda_min_iterative"])
            if isinstance(best_global, dict) and isinstance(best_global.get("lambda_min_iterative"), (int, float))
            else None
        ),
        "best_low_lambda_rows": [
            {
                "frame": int(row["frame"]),
                "snapshot_index": int(row["snapshot_index"]),
                "shell": int(row["shell"]),
                "profile_id": row.get("best_low_lambda_profile", {}).get("profile_id")
                if isinstance(row.get("best_low_lambda_profile"), dict)
                else None,
                "lambda_min_iterative": (
                    float(row["best_low_lambda_profile"]["lambda_min_iterative"])
                    if isinstance(row.get("best_low_lambda_profile"), dict)
                    and isinstance(row.get("best_low_lambda_profile", {}).get("lambda_min_iterative"), (int, float))
                    else None
                ),
                "tail_escape_candidate_count": int(row.get("tail_escape_candidate_count", 0)),
                "worst_eigenvector_shell_iterative": (
                    float(row["best_low_lambda_profile"]["worst_eigenvector_shell_iterative"])
                    if isinstance(row.get("best_low_lambda_profile"), dict)
                    and isinstance(row.get("best_low_lambda_profile", {}).get("worst_eigenvector_shell_iterative"), (int, float))
                    else None
                ),
            }
            for row in sorted(
                rows,
                key=lambda row_item: (
                    float("inf")
                    if not isinstance(row_item.get("best_low_lambda_profile"), dict)
                    or not isinstance(row_item.get("best_low_lambda_profile", {}).get("lambda_min_iterative"), (int, float))
                    else float(row_item["best_low_lambda_profile"]["lambda_min_iterative"]),
                    -int(row_item.get("tail_escape_candidate_count", 0)),
                ),
            )
            if isinstance(row.get("best_low_lambda_profile"), dict)
            and isinstance(row.get("best_low_lambda_profile", {}).get("lambda_min_iterative"), (int, float))
        ],
        "best_profile_worst_shells": worst_shells,
        "worst_shell_progression_max": max(worst_shells) if worst_shells else None,
        "candidate_only": True,
        "fail_closed": True,
        "gpu_kn_authority": False,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "dense_reconstruction_used_by_iterative_lane": False,
        "dense_eigensolve_scope": "small_shell_oracle_only",
        "tail_adversary_status": "fail-closed" if parity_mismatches else "candidate-tail-telemetry",
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells if args.shells is not None else list(DEFAULT_SHELLS))
    seeds = [int(seed) for seed in (args.seeds if args.seeds is not None else list(DEFAULT_SEEDS))]
    c0_values = [float(value) for value in args.c0_values]
    tail_cutoffs = sorted({int(value) for value in args.tail_cutoffs})
    tail_etas = [float(value) for value in args.tail_etas]
    warnings: list[str] = []
    force_tail_profiles = bool(args.force_tail_profiles) and not bool(args.no_force_tail_profiles)
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
            tail_cutoffs=tail_cutoffs,
            tail_etas=tail_etas,
            r0=float(args.r0),
            d0=float(args.d0),
            parity_tol=float(args.parity_tol),
            lobpcg_tol=float(args.lobpcg_tol),
            lobpcg_maxiter=int(args.lobpcg_maxiter),
            block_size=int(args.block_size),
            generalized_mass_shift=float(args.generalized_mass_shift),
            dense_oracle_shell_limit=int(args.dense_oracle_shell_limit),
            gpu_checks=int(args.gpu_matvec_checks),
            max_profiles_per_row=int(args.max_profiles_per_row),
            profile_sample_limit=int(args.profile_sample_limit),
            tail_grid_detail=str(args.tail_grid_detail),
            force_tail_profiles=force_tail_profiles,
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
            "seeds": seeds,
            "shells": [int(shell) for shell in shells],
            "c0_values": c0_values,
            "tail_cutoffs": tail_cutoffs,
            "tail_etas": tail_etas,
            "r0": float(args.r0),
            "d0": float(args.d0),
            "parity_tol": float(args.parity_tol),
            "lobpcg_tol": float(args.lobpcg_tol),
            "lobpcg_maxiter": int(args.lobpcg_maxiter),
            "block_size": int(args.block_size),
            "generalized_mass_shift": float(args.generalized_mass_shift),
            "dense_oracle_shell_limit": int(args.dense_oracle_shell_limit),
            "gpu_matvec_checks": int(args.gpu_matvec_checks),
            "profile_sample_limit": int(args.profile_sample_limit),
            "max_profiles_per_row": int(args.max_profiles_per_row),
            "tail_grid_detail": str(args.tail_grid_detail),
            "force_tail_profiles": force_tail_profiles,
        },
        "tail_grid_detail": str(args.tail_grid_detail),
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
