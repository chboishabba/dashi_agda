#!/usr/bin/env python3
"""Matrix-free generalized K_N(A) eigen scan for NS triad carriers.

This lane replaces full K_N(A) materialization with the generalized problem

    L_neg(A) x = lambda L_abs(A) x.

For N=2,3 it still computes a dense CPU oracle as a parity receipt.  The
``vulkan-matvec`` backend uses an incidence-aware Vulkan matvec, but GPU
authority is explicitly false until dense CPU, CPU matrix-free, and GPU matvec
receipts all agree.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
from ns_orbit_phase_coherence_scan import ModeRecord  # type: ignore
from ns_triad_cocycle_floor_scan import _validate_shells  # type: ignore
from ns_triad_constrained_adversarial_fork_optimizer import (  # type: ignore
    DEFAULT_D0,
    DEFAULT_HIGH_SHELL_CUTOFF,
    DEFAULT_HIGH_SHELL_ETA,
    DEFAULT_R0,
    _branch,
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
from ns_triad_kn_matrix_free_operator import (  # type: ignore
    MatrixFreeKNProfile,
    build_profile,
    dense_parity_adapter,
    matvec_abs,
    matvec_neg,
)

try:
    from gpu_vulkan_triad_laplacian import (  # type: ignore
        VulkanTriadLaplacianExecutor,
        create_vulkan_triad_laplacian_executor,
        has_vulkan_triad_laplacian,
    )
except Exception:  # pragma: no cover - optional Vulkan runtime
    VulkanTriadLaplacianExecutor = None  # type: ignore
    create_vulkan_triad_laplacian_executor = None  # type: ignore

    def has_vulkan_triad_laplacian() -> bool:  # type: ignore
        return False


SCRIPT_NAME = "scripts/ns_triad_kn_lobpcg_scan.py"
CONTRACT = "ns_triad_kn_lobpcg_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_MATRIX_FREE_LOBPCG_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_lobpcg_scan_N128_20260623.json"
)
DEFAULT_SHELLS = (2, 3)
DEFAULT_SAMPLE_COUNT = 24
DEFAULT_MIX_COUNT = 4
DEFAULT_SEEDS = (0, 1)
DEFAULT_PARITY_TOL = 1.0e-9

CONTROL_CARD = {
    "O": "Add a matrix-free K_N(A) eigen lane for finite NS triad carriers.",
    "R": (
        "Solve L_neg(A) x = lambda L_abs(A) x with matrix-free matvecs, using dense CPU only "
        "as a small-shell N=2,3 oracle."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only numerical receipt; no theorem, full-NS, or Clay promotion is inferred.",
    "L": (
        "Load shell carriers, sample profiles, build weighted incidence matvecs, compute bottom "
        "generalized eigenpairs, compare against dense CPU parity, and fail closed on mismatch."
    ),
    "P": ROUTE_DECISION,
    "G": "GPU matvecs are non-authoritative until backend parity is implemented and passing.",
    "F": "This is runtime acceleration and parity telemetry only; all analytic K_N obligations remain open.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument(
        "--kn-backend",
        choices=("dense", "cpu-matrix-free", "vulkan-matvec"),
        default="cpu-matrix-free",
    )
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=1)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--mix-count", type=int, default=DEFAULT_MIX_COUNT)
    parser.add_argument("--profile-sample-limit", type=int, default=8)
    parser.add_argument("--seed", dest="seeds", action="append", type=int, default=None)
    parser.add_argument("--d0", type=float, default=DEFAULT_D0)
    parser.add_argument("--r0", type=float, default=DEFAULT_R0)
    parser.add_argument("--high-shell-cutoff", type=float, default=DEFAULT_HIGH_SHELL_CUTOFF)
    parser.add_argument("--high-shell-eta", type=float, default=DEFAULT_HIGH_SHELL_ETA)
    parser.add_argument("--parity-tol", type=float, default=DEFAULT_PARITY_TOL)
    parser.add_argument(
        "--shell",
        dest="shells",
        action="append",
        type=int,
        default=None,
        help="Shell cutoff N to evaluate; may be repeated. Defaults to 2 and 3.",
    )
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _matvec_dense_matrix(matvec: Any, n: int) -> np.ndarray:
    matrix = np.zeros((n, n), dtype=np.float64)
    for index in range(n):
        basis = np.zeros(n, dtype=np.float64)
        basis[index] = 1.0
        matrix[:, index] = matvec(basis)
    return 0.5 * (matrix + matrix.T)


def _generalized_from_laplacians(
    l_abs: np.ndarray,
    l_neg: np.ndarray,
    profile: MatrixFreeKNProfile,
    zero_eps: float,
    positive_tol: float | None = None,
) -> dict[str, Any]:
    evals, basis = np.linalg.eigh(l_abs)
    tol = max(float(zero_eps), 1.0e-10 if positive_tol is None else float(positive_tol))
    mask = np.asarray(evals > tol, dtype=bool)
    if not np.any(mask):
        return {
            "status": PARTIAL_STATUS,
            "lambda_min": None,
            "lambda_max": None,
            "l_abs_positive_rank": 0,
            "worst_eigenvector_shell": None,
            "worst_eigenvector_shell_mass_fraction": None,
            "warnings": ["l_abs_has_no_positive_subspace"],
        }
    pos_evals = np.asarray(evals[mask], dtype=np.float64)
    pos_basis = np.asarray(basis[:, mask], dtype=np.float64)
    reduced_abs_neg = (pos_basis * (1.0 / np.sqrt(pos_evals))).T @ l_neg @ (
        pos_basis * (1.0 / np.sqrt(pos_evals))
    )
    reduced_abs_neg = 0.5 * (reduced_abs_neg + reduced_abs_neg.T)
    eigs, evecs = np.linalg.eigh(reduced_abs_neg)
    worst_index = int(np.argmin(eigs))
    full_vec = np.asarray((pos_basis * (1.0 / np.sqrt(pos_evals))) @ evecs[:, worst_index], dtype=np.float64)
    norm = float(np.linalg.norm(full_vec))
    if norm > float(zero_eps):
        full_vec = full_vec / norm
    shell = None
    shell_mass_fraction = None
    if profile.shell_levels is not None:
        masses = full_vec * full_vec
        total_mass = float(np.sum(masses))
        shell_mass: dict[int, float] = {}
        for shell_value, mass in zip(profile.shell_levels, masses, strict=False):
            key = int(shell_value)
            shell_mass[key] = shell_mass.get(key, 0.0) + float(mass)
        if shell_mass:
            shell, value = max(shell_mass.items(), key=lambda item: item[1])
            shell_mass_fraction = float(value / max(total_mass, float(zero_eps)))
    return {
        "status": OK_STATUS,
        "lambda_min": float(np.min(eigs)),
        "lambda_max": float(np.max(eigs)),
        "l_abs_positive_rank": int(len(pos_evals)),
        "worst_eigenvector_shell": shell,
        "worst_eigenvector_shell_mass_fraction": shell_mass_fraction,
        "warnings": [],
    }


def _matrix_free_generalized(profile: MatrixFreeKNProfile, zero_eps: float) -> dict[str, Any]:
    """CPU matrix-free parity solve; dense only materializes L_abs/L_neg, not K_N."""

    n = int(profile.mode_count)
    l_abs = _matvec_dense_matrix(lambda vec: matvec_abs(vec, profile), n)
    l_neg = _matvec_dense_matrix(lambda vec: matvec_neg(vec, profile), n)
    return _generalized_from_laplacians(l_abs, l_neg, profile, zero_eps)


def _vulkan_generalized(profile: MatrixFreeKNProfile, zero_eps: float) -> dict[str, Any]:
    if (
        VulkanTriadLaplacianExecutor is None
        or create_vulkan_triad_laplacian_executor is None
        or not has_vulkan_triad_laplacian()
    ):
        return {
            "status": PARTIAL_STATUS,
            "lambda_min": None,
            "lambda_max": None,
            "l_abs_positive_rank": 0,
            "worst_eigenvector_shell": None,
            "worst_eigenvector_shell_mass_fraction": None,
            "gpu_matvec_max_abs_error_abs": None,
            "gpu_matvec_max_abs_error_neg": None,
            "gpu_matvec_parity_ok": False,
            "vulkan_icd": None,
            "icd_probe_errors": [],
            "warnings": ["vulkan_triad_laplacian_unavailable"],
        }

    n = int(profile.mode_count)
    try:
        executor, probe_info = create_vulkan_triad_laplacian_executor(profile)
    except Exception as exc:  # noqa: BLE001
        return {
            "status": PARTIAL_STATUS,
            "lambda_min": None,
            "lambda_max": None,
            "l_abs_positive_rank": 0,
            "worst_eigenvector_shell": None,
            "worst_eigenvector_shell_mass_fraction": None,
            "gpu_matvec_max_abs_error_abs": None,
            "gpu_matvec_max_abs_error_neg": None,
            "gpu_matvec_parity_ok": False,
            "vulkan_icd": None,
            "icd_probe_errors": [],
            "warnings": [f"vulkan_triad_laplacian_init_failed: {type(exc).__name__}: {exc}"],
        }
    try:
        l_abs_gpu = _matvec_dense_matrix(executor.matvec_abs, n)
        l_neg_gpu = _matvec_dense_matrix(executor.matvec_neg, n)
    finally:
        executor.close()
    l_abs_cpu = _matvec_dense_matrix(lambda vec: matvec_abs(vec, profile), n)
    l_neg_cpu = _matvec_dense_matrix(lambda vec: matvec_neg(vec, profile), n)
    abs_error = float(np.max(np.abs(l_abs_gpu - l_abs_cpu))) if n else 0.0
    neg_error = float(np.max(np.abs(l_neg_gpu - l_neg_cpu))) if n else 0.0
    result = _generalized_from_laplacians(l_abs_gpu, l_neg_gpu, profile, zero_eps, positive_tol=1.0e-6)
    result["gpu_matvec_max_abs_error_abs"] = abs_error
    result["gpu_matvec_max_abs_error_neg"] = neg_error
    result["gpu_matvec_parity_ok"] = bool(abs_error <= 5.0e-5 and neg_error <= 5.0e-5)
    result["vulkan_icd"] = probe_info.get("vulkan_icd")
    result["icd_probe_errors"] = probe_info.get("icd_probe_errors", [])
    if not result["gpu_matvec_parity_ok"]:
        result["warnings"] = list(result.get("warnings", [])) + ["vulkan_matvec_cpu_parity_mismatch"]
    return result


def _backend_parity_ok(
    backend: str,
    dense: dict[str, Any],
    matrix_free: dict[str, Any],
    relative_error: float | None,
    absolute_error: float | None,
    branch_agrees: bool,
    shell_agrees: bool,
    parity_tol: float,
) -> bool:
    eigen_agrees = bool(
        relative_error is not None
        and absolute_error is not None
        and (relative_error <= float(parity_tol) or absolute_error <= float(parity_tol))
    )
    common = bool(
        dense["status"] == OK_STATUS
        and matrix_free["status"] == OK_STATUS
        and eigen_agrees
        and branch_agrees
        and shell_agrees
    )
    if backend == "vulkan-matvec":
        return bool(common and matrix_free.get("gpu_matvec_parity_ok") is True)
    return common


def _evaluate(
    triads: list[Any],
    probability: np.ndarray,
    shell_levels: np.ndarray,
    profile_id: str,
    backend: str,
    zero_eps: float,
    high_shell_cutoff: float,
    r0: float,
    high_shell_eta: float,
    d0: float,
    parity_tol: float,
) -> dict[str, Any]:
    profile = build_profile(
        triads=triads,
        probability=probability,
        mode_count=int(len(probability)),
        zero_eps=zero_eps,
        shell_levels=shell_levels,
        profile_id=profile_id,
    )
    dense = dense_parity_adapter(profile, zero_eps=zero_eps)
    if backend == "dense":
        matrix_free = {
            "status": dense["status"],
            "lambda_min": dense.get("lambda_min"),
            "lambda_max": dense.get("lambda_max"),
            "l_abs_positive_rank": dense.get("l_abs_positive_rank"),
            "worst_eigenvector_shell": dense.get("worst_eigenvector_shell"),
            "worst_eigenvector_shell_mass_fraction": dense.get("worst_eigenvector_shell_mass_fraction"),
            "warnings": dense.get("warnings", []),
        }
    elif backend == "vulkan-matvec":
        matrix_free = _vulkan_generalized(profile, zero_eps)
    else:
        matrix_free = _matrix_free_generalized(profile, zero_eps)

    dense_lambda = dense.get("lambda_min")
    mf_lambda = matrix_free.get("lambda_min")
    relative_error = None
    absolute_error = None
    if isinstance(dense_lambda, (int, float)) and isinstance(mf_lambda, (int, float)):
        absolute_error = float(abs(float(mf_lambda) - float(dense_lambda)))
        relative_error = float(absolute_error / max(abs(float(dense_lambda)), 1.0e-12))

    metrics = _profile_metrics(probability, shell_levels, zero_eps, high_shell_cutoff)
    dense_branch_input = {**metrics, "lambda_min_kn_a": dense_lambda, "status": dense["status"]}
    mf_branch_input = {**metrics, "lambda_min_kn_a": mf_lambda, "status": matrix_free["status"]}
    dense_branch = _branch(dense_branch_input, c0=0.25, r0=r0, high_shell_eta=high_shell_eta, d0=d0)
    mf_branch = _branch(mf_branch_input, c0=0.25, r0=r0, high_shell_eta=high_shell_eta, d0=d0)
    shell_agrees = dense.get("worst_eigenvector_shell") == matrix_free.get("worst_eigenvector_shell")
    branch_agrees = dense_branch == mf_branch
    parity_ok = _backend_parity_ok(
        backend,
        dense,
        matrix_free,
        relative_error,
        absolute_error,
        branch_agrees,
        shell_agrees,
        parity_tol,
    )
    return {
        "profile_id": profile_id,
        "status": OK_STATUS if parity_ok else PARTIAL_STATUS,
        "candidate_only": True,
        "fail_closed": True,
        "kn_backend": backend,
        "gpu_kn_authority": False,
        "edge_count": int(len(profile.weights_abs)),
        "l_abs_positive_rank": matrix_free.get("l_abs_positive_rank"),
        "lambda_min_dense_cpu": dense_lambda,
        "lambda_min_matrix_free": mf_lambda,
        "lambda_max_matrix_free": matrix_free.get("lambda_max"),
        "absolute_error_vs_dense": absolute_error,
        "relative_error_vs_dense": relative_error,
        "branch_classification_dense_cpu": dense_branch,
        "branch_classification_matrix_free": mf_branch,
        "branch_classification_agrees": branch_agrees,
        "worst_eigenvector_shell_dense_cpu": dense.get("worst_eigenvector_shell"),
        "worst_eigenvector_shell_matrix_free": matrix_free.get("worst_eigenvector_shell"),
        "worst_eigenvector_shell_mass_dense_cpu": dense.get("worst_eigenvector_shell_mass_fraction"),
        "worst_eigenvector_shell_mass_matrix_free": matrix_free.get("worst_eigenvector_shell_mass_fraction"),
        "worst_eigenvector_shell_mass_agrees": shell_agrees,
        "gpu_matvec_max_abs_error_abs": matrix_free.get("gpu_matvec_max_abs_error_abs"),
        "gpu_matvec_max_abs_error_neg": matrix_free.get("gpu_matvec_max_abs_error_neg"),
        "gpu_matvec_parity_ok": matrix_free.get("gpu_matvec_parity_ok"),
        "vulkan_icd": matrix_free.get("vulkan_icd"),
        "icd_probe_errors": matrix_free.get("icd_probe_errors"),
        "parity_ok": parity_ok,
        "warnings": list(dense.get("warnings", [])) + list(matrix_free.get("warnings", [])),
        "metrics": metrics,
    }


def _row(
    slot: int,
    snapshot: int,
    bundle: Any,
    shell_n: int,
    backend: str,
    zero_eps: float,
    sample_count: int,
    mix_count: int,
    seeds: list[int],
    high_shell_cutoff: float,
    r0: float,
    high_shell_eta: float,
    d0: float,
    parity_tol: float,
    profile_sample_limit: int,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "shell": int(shell_n),
        "kn_backend": backend,
        "candidate_only": True,
        "fail_closed": True,
        "gpu_kn_authority": False,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        shell_modes: list[ModeRecord] = _cube_modes(spectrum, shell_n=shell_n, zero_eps=zero_eps)
        triads, _frame_metrics = _build_frame_surface(shell_modes, zero_eps=zero_eps, triad_sample_limit=8)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"kn_lobpcg_scan_error: {exc}"]
        return row

    row["selected_mode_count"] = int(len(shell_modes))
    row["triad_count"] = int(len(triads))
    if len(shell_modes) < 3 or not triads:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_insufficient_modes"]
        row["profile_count"] = 0
        row["parity_ok_count"] = 0
        return row

    amplitudes = np.asarray([float(mode.amplitude) for mode in shell_modes], dtype=np.float64)
    base_probability = _normalize_profile(amplitudes * amplitudes, zero_eps)
    shell_radii = np.asarray([float(mode.shell_radius) for mode in shell_modes], dtype=np.float64)
    levels = _shell_levels(shell_radii)
    evaluated: list[dict[str, Any]] = []
    seen: set[str] = set()
    for seed in seeds:
        profiles = _candidate_profiles(base_probability, levels, sample_count, mix_count, seed, zero_eps)
        for profile_id, probability in profiles:
            unique_id = f"seed{seed}:{profile_id}"
            if unique_id in seen:
                continue
            seen.add(unique_id)
            evaluated.append(
                _evaluate(
                    triads=triads,
                    probability=probability,
                    shell_levels=levels,
                    profile_id=unique_id,
                    backend=backend,
                    zero_eps=zero_eps,
                    high_shell_cutoff=high_shell_cutoff,
                    r0=r0,
                    high_shell_eta=high_shell_eta,
                    d0=d0,
                    parity_tol=parity_tol,
                )
            )
    ok_profiles = [item for item in evaluated if item.get("parity_ok") is True]
    best = min(
        (item for item in evaluated if isinstance(item.get("lambda_min_matrix_free"), (int, float))),
        key=lambda item: float(item["lambda_min_matrix_free"]),
        default=None,
    )
    row.update(
        {
            "status": OK_STATUS if len(ok_profiles) == len(evaluated) and evaluated else PARTIAL_STATUS,
            "profile_count": int(len(evaluated)),
            "parity_ok_count": int(len(ok_profiles)),
            "parity_mismatch_count": int(len(evaluated) - len(ok_profiles)),
            "best_profile": best,
            "profile_samples": evaluated[: min(max(0, int(profile_sample_limit)), len(evaluated))],
        }
    )
    return row


def _aggregate(rows: list[dict[str, Any]], backend: str) -> dict[str, Any]:
    total_profiles = sum(int(row.get("profile_count", 0)) for row in rows)
    parity_ok = sum(int(row.get("parity_ok_count", 0)) for row in rows)
    mismatches = sum(int(row.get("parity_mismatch_count", 0)) for row in rows)
    return {
        "processed_rows": int(len(rows)),
        "ok_rows": int(sum(1 for row in rows if row.get("status") == OK_STATUS)),
        "partial_rows": int(sum(1 for row in rows if row.get("status") == PARTIAL_STATUS)),
        "error_rows": int(sum(1 for row in rows if row.get("status") == ERROR_STATUS)),
        "kn_backend": backend,
        "sampled_profile_count": int(total_profiles),
        "parity_ok_count": int(parity_ok),
        "parity_mismatch_count": int(mismatches),
        "all_cpu_parity_passed": bool(backend != "vulkan-matvec" and total_profiles > 0 and mismatches == 0),
        "gpu_kn_authority": False,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "kn_matrix_free_status": "fail-closed" if mismatches else "candidate-parity",
        "dense_eigensolve_scope": "small_shell_oracle_only",
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells if args.shells is not None else list(DEFAULT_SHELLS))
    seeds = [int(seed) for seed in (args.seeds if args.seeds is not None else list(DEFAULT_SEEDS))]
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
            high_shell_cutoff=float(args.high_shell_cutoff),
            r0=float(args.r0),
            high_shell_eta=float(args.high_shell_eta),
            d0=float(args.d0),
            parity_tol=float(args.parity_tol),
            profile_sample_limit=int(args.profile_sample_limit),
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
            "frame_limit": args.frame_limit,
            "zero_eps": float(args.zero_eps),
            "sample_count": int(args.sample_count),
            "mix_count": int(args.mix_count),
            "profile_sample_limit": int(args.profile_sample_limit),
            "seeds": seeds,
            "shells": [int(shell) for shell in shells],
            "d0": float(args.d0),
            "r0": float(args.r0),
            "high_shell_cutoff": float(args.high_shell_cutoff),
            "high_shell_eta": float(args.high_shell_eta),
            "parity_tol": float(args.parity_tol),
        },
        "status": ERROR_STATUS if any(row.get("status") == ERROR_STATUS for row in rows) else (
            OK_STATUS if all(row.get("status") == OK_STATUS for row in rows) else PARTIAL_STATUS
        ),
        "rows": rows,
        "aggregate": _aggregate(rows, backend=args.kn_backend),
        "warnings": warnings,
        "errors": [error for row in rows for error in row.get("errors", [])],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, pretty=args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0 if payload["status"] != ERROR_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
