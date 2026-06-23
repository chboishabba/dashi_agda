#!/usr/bin/env python3
"""Iterative matrix-free generalized K_N(A) eigen scan for NS triads.

This scan solves

    L_neg(A) x = lambda L_abs(A) x

with SciPy LOBPCG over matvec-only CPU or Vulkan backends.  Dense CPU solves are
kept only as optional small-shell oracle receipts; the iterative lane does not
materialize L_abs, L_neg, or K_N(A).
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import time
from typing import Any, Callable
import warnings

import numpy as np
from scipy.sparse.linalg import LinearOperator, lobpcg

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
        create_vulkan_triad_laplacian_executor,
        has_vulkan_triad_laplacian,
    )
except Exception:  # pragma: no cover - optional Vulkan runtime
    create_vulkan_triad_laplacian_executor = None  # type: ignore

    def has_vulkan_triad_laplacian() -> bool:  # type: ignore
        return False


SCRIPT_NAME = "scripts/ns_triad_kn_iterative_generalized_eig.py"
CONTRACT = "ns_triad_kn_iterative_generalized_eig"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_ITERATIVE_GENERALIZED_EIG_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_iterative_generalized_eig_N128_20260623.json"
)
DEFAULT_SHELLS = (2, 3, 4)
DEFAULT_SAMPLE_COUNT = 8
DEFAULT_MIX_COUNT = 2
DEFAULT_SEEDS = (0,)
DEFAULT_PARITY_TOL = 1.0e-6
DEFAULT_LOBPCG_TOL = 1.0e-7
DEFAULT_LOBPCG_MAXITER = 80
DEFAULT_GENERALIZED_MASS_SHIFT = 1.0e-8

CONTROL_CARD = {
    "O": "Run the K_N(A) generalized eigen lane without dense operator reconstruction.",
    "R": (
        "Use L_neg(A) and L_abs(A) matvecs directly in LOBPCG, with dense CPU solves only as "
        "small-shell parity oracles."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only runtime telemetry; no theorem, full-NS, or Clay promotion is inferred.",
    "L": (
        "Load shell carriers, build weighted incidence profiles, call CPU or Vulkan matvecs through "
        "LinearOperator, compute bottom generalized eigenpairs, and compare small shells to dense parity."
    ),
    "P": ROUTE_DECISION,
    "G": "GPU matvecs remain non-authoritative and gpu_kn_authority is always false.",
    "F": "This removes dense reconstruction from the runtime lane only; analytic no-triple-danger remains open.",
}


class BackendMatvec:
    def __init__(
        self,
        *,
        name: str,
        abs_mv: Callable[[np.ndarray], np.ndarray],
        neg_mv: Callable[[np.ndarray], np.ndarray],
        abs_mm: Callable[[np.ndarray], np.ndarray] | None = None,
        neg_mm: Callable[[np.ndarray], np.ndarray] | None = None,
        close: Callable[[], None] | None = None,
        info: dict[str, Any] | None = None,
    ) -> None:
        self.name = name
        self.abs_mv = abs_mv
        self.neg_mv = neg_mv
        self.abs_mm = abs_mm or (lambda matrix: np.column_stack([abs_mv(matrix[:, column]) for column in range(matrix.shape[1])]))
        self.neg_mm = neg_mm or (lambda matrix: np.column_stack([neg_mv(matrix[:, column]) for column in range(matrix.shape[1])]))
        self.close = close or (lambda: None)
        self.info = info or {}


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
    parser.add_argument("--profile-sample-limit", type=int, default=6)
    parser.add_argument("--max-profiles-per-row", type=int, default=0)
    parser.add_argument("--seed", dest="seeds", action="append", type=int, default=None)
    parser.add_argument("--d0", type=float, default=DEFAULT_D0)
    parser.add_argument("--r0", type=float, default=DEFAULT_R0)
    parser.add_argument("--high-shell-cutoff", type=float, default=DEFAULT_HIGH_SHELL_CUTOFF)
    parser.add_argument("--high-shell-eta", type=float, default=DEFAULT_HIGH_SHELL_ETA)
    parser.add_argument("--parity-tol", type=float, default=DEFAULT_PARITY_TOL)
    parser.add_argument("--lobpcg-tol", type=float, default=DEFAULT_LOBPCG_TOL)
    parser.add_argument("--lobpcg-maxiter", type=int, default=DEFAULT_LOBPCG_MAXITER)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--generalized-mass-shift", type=float, default=DEFAULT_GENERALIZED_MASS_SHIFT)
    parser.add_argument("--dense-oracle-shell-limit", type=int, default=3)
    parser.add_argument("--gpu-matvec-checks", type=int, default=2)
    parser.add_argument(
        "--shell",
        dest="shells",
        action="append",
        type=int,
        default=None,
        help="Shell cutoff N to evaluate; may be repeated. Defaults to 2, 3, and 4.",
    )
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _operator_from_matvec(
    matvec: Callable[[np.ndarray], np.ndarray],
    matmat: Callable[[np.ndarray], np.ndarray] | None,
    n: int,
) -> LinearOperator:
    def apply(array: np.ndarray) -> np.ndarray:
        values = np.asarray(array, dtype=np.float64)
        if values.ndim == 1:
            return np.asarray(matvec(values), dtype=np.float64)
        if values.ndim == 2:
            if values.shape[1] == 0:
                return np.zeros((n, 0), dtype=np.float64)
            if matmat is not None:
                return np.asarray(matmat(values), dtype=np.float64)
            return np.column_stack([np.asarray(matvec(values[:, column]), dtype=np.float64) for column in range(values.shape[1])])
        raise ValueError(f"operator input must be vector or matrix, got ndim={values.ndim}")

    def mv(vec: np.ndarray) -> np.ndarray:
        return apply(vec)

    def mm(matrix: np.ndarray) -> np.ndarray:
        return apply(matrix)

    return LinearOperator((n, n), matvec=mv, matmat=mm, dtype=np.float64)


def _shifted_operator_from_matvec(
    matvec: Callable[[np.ndarray], np.ndarray],
    matmat: Callable[[np.ndarray], np.ndarray] | None,
    n: int,
    shift: float,
) -> LinearOperator:
    def shifted(array: np.ndarray) -> np.ndarray:
        values = np.asarray(array, dtype=np.float64)
        return np.asarray(matvec(values), dtype=np.float64) + float(shift) * values

    def shifted_matmat(matrix: np.ndarray) -> np.ndarray:
        values = np.asarray(matrix, dtype=np.float64)
        base = np.asarray(matmat(values), dtype=np.float64) if matmat is not None else np.column_stack(
            [np.asarray(matvec(values[:, column]), dtype=np.float64) for column in range(values.shape[1])]
        )
        return base + float(shift) * values

    return _operator_from_matvec(shifted, shifted_matmat, n)


def _shell_localization(vector: np.ndarray, profile: MatrixFreeKNProfile, zero_eps: float) -> tuple[int | None, float | None]:
    if profile.shell_levels is None:
        return None, None
    vec = np.asarray(vector, dtype=np.float64)
    norm = float(np.linalg.norm(vec))
    if norm > float(zero_eps):
        vec = vec / norm
    masses = vec * vec
    total_mass = float(np.sum(masses))
    shell_mass: dict[int, float] = {}
    for shell_value, mass in zip(profile.shell_levels, masses, strict=False):
        key = int(shell_value)
        shell_mass[key] = shell_mass.get(key, 0.0) + float(mass)
    if not shell_mass:
        return None, None
    shell, mass = max(shell_mass.items(), key=lambda item: item[1])
    return int(shell), float(mass / max(total_mass, float(zero_eps)))


def _make_backend(profile: MatrixFreeKNProfile, backend: str, zero_eps: float, gpu_checks: int) -> BackendMatvec:
    if backend == "cpu-matrix-free":
        cpu_abs_mv = lambda vec: matvec_abs(vec, profile)
        cpu_neg_mv = lambda vec: matvec_neg(vec, profile)
        return BackendMatvec(
            name=backend,
            abs_mv=cpu_abs_mv,
            neg_mv=cpu_neg_mv,
            abs_mm=lambda matrix: np.column_stack([cpu_abs_mv(matrix[:, column]) for column in range(matrix.shape[1])]),
            neg_mm=lambda matrix: np.column_stack([cpu_neg_mv(matrix[:, column]) for column in range(matrix.shape[1])]),
            info={
                "gpu_matvec_parity_ok": None,
                "gpu_matvec_max_abs_error_abs": None,
                "gpu_matvec_max_abs_error_neg": None,
                "vulkan_icd": None,
                "icd_probe_errors": None,
                "block_matvec_enabled": True,
                "block_matvec_backend": "cpu-column-loop",
                "gpu_block_matvec_parity_ok": None,
                "gpu_block_matvec_max_abs_error_abs": None,
                "gpu_block_matvec_max_abs_error_neg": None,
            },
        )
    if create_vulkan_triad_laplacian_executor is None or not has_vulkan_triad_laplacian():
        raise RuntimeError("vulkan_triad_laplacian_unavailable")
    executor, probe_info = create_vulkan_triad_laplacian_executor(profile)
    rng = np.random.default_rng(12345)
    abs_errors: list[float] = []
    neg_errors: list[float] = []
    block_abs_errors: list[float] = []
    block_neg_errors: list[float] = []
    for _ in range(max(0, int(gpu_checks))):
        vec = rng.normal(size=int(profile.mode_count))
        norm = float(np.linalg.norm(vec))
        if norm > float(zero_eps):
            vec = vec / norm
        abs_errors.append(float(np.max(np.abs(executor.matvec_abs(vec) - matvec_abs(vec, profile)))))
        neg_errors.append(float(np.max(np.abs(executor.matvec_neg(vec) - matvec_neg(vec, profile)))))
        block = rng.normal(size=(int(profile.mode_count), 3))
        block_norms = np.linalg.norm(block, axis=0)
        for column, norm_value in enumerate(block_norms):
            if float(norm_value) > float(zero_eps):
                block[:, column] /= float(norm_value)
        cpu_abs_block = np.column_stack([matvec_abs(block[:, column], profile) for column in range(block.shape[1])])
        cpu_neg_block = np.column_stack([matvec_neg(block[:, column], profile) for column in range(block.shape[1])])
        block_abs_errors.append(float(np.max(np.abs(executor.matmat_abs(block) - cpu_abs_block))))
        block_neg_errors.append(float(np.max(np.abs(executor.matmat_neg(block) - cpu_neg_block))))
    abs_error = max(abs_errors) if abs_errors else None
    neg_error = max(neg_errors) if neg_errors else None
    block_abs_error = max(block_abs_errors) if block_abs_errors else None
    block_neg_error = max(block_neg_errors) if block_neg_errors else None
    scalar_parity_ok = bool(
        abs_error is not None
        and neg_error is not None
        and abs_error <= 5.0e-5
        and neg_error <= 5.0e-5
    )
    block_parity_ok = bool(
        block_abs_error is not None
        and block_neg_error is not None
        and block_abs_error <= 5.0e-5
        and block_neg_error <= 5.0e-5
    )
    return BackendMatvec(
        name=backend,
        abs_mv=executor.matvec_abs,
        neg_mv=executor.matvec_neg,
        abs_mm=executor.matmat_abs,
        neg_mm=executor.matmat_neg,
        close=executor.close,
        info={
            "gpu_matvec_parity_ok": bool(scalar_parity_ok and block_parity_ok),
            "gpu_matvec_max_abs_error_abs": abs_error,
            "gpu_matvec_max_abs_error_neg": neg_error,
            "vulkan_icd": probe_info.get("vulkan_icd"),
            "icd_probe_errors": probe_info.get("icd_probe_errors", []),
            "block_matvec_enabled": True,
            "block_matvec_backend": "vulkan-csr-block",
            "gpu_block_matvec_parity_ok": block_parity_ok,
            "gpu_block_matvec_max_abs_error_abs": block_abs_error,
            "gpu_block_matvec_max_abs_error_neg": block_neg_error,
        },
    )


def _iterative_generalized(
    profile: MatrixFreeKNProfile,
    backend: str,
    zero_eps: float,
    lobpcg_tol: float,
    lobpcg_maxiter: int,
    block_size: int,
    generalized_mass_shift: float,
    gpu_checks: int,
) -> dict[str, Any]:
    n = int(profile.mode_count)
    if n < 3:
        return {
            "status": PARTIAL_STATUS,
            "lambda_min": None,
            "lambda_max": None,
            "worst_eigenvector_shell": None,
            "worst_eigenvector_shell_mass_fraction": None,
            "iterations": 0,
            "residual_norm": None,
            "warnings": ["mode_count_too_small"],
        }
    started = time.perf_counter()
    backend_handle: BackendMatvec | None = None
    try:
        backend_handle = _make_backend(profile, backend, zero_eps, gpu_checks)
        a_op = _operator_from_matvec(backend_handle.neg_mv, backend_handle.neg_mm, n)
        b_op = _shifted_operator_from_matvec(
            backend_handle.abs_mv,
            backend_handle.abs_mm,
            n,
            max(float(generalized_mass_shift), 0.0),
        )
        k = max(1, min(int(block_size), n - 2))
        rng = np.random.default_rng(abs(hash(profile.profile_id)) % (2**32))
        x0 = rng.normal(size=(n, k))
        y = np.ones((n, 1), dtype=np.float64)
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            eigs, vecs, lambda_history, residual_history = lobpcg(
                a_op,
                x0,
                B=b_op,
                Y=y,
                tol=float(lobpcg_tol),
                maxiter=int(lobpcg_maxiter),
                largest=False,
                retLambdaHistory=True,
                retResidualNormsHistory=True,
                restartControl=20,
            )
        vecs = np.asarray(vecs, dtype=np.float64)
        rayleighs: list[float] = []
        residuals: list[float] = []
        for column in range(vecs.shape[1]):
            vec = vecs[:, column]
            av_col = np.asarray(backend_handle.neg_mv(vec), dtype=np.float64)
            bv_col = np.asarray(backend_handle.abs_mv(vec), dtype=np.float64)
            denominator_col = float(vec @ bv_col)
            rq = (
                float((vec @ av_col) / denominator_col)
                if abs(denominator_col) > float(zero_eps)
                else float("inf")
            )
            rayleighs.append(rq)
            residuals.append(float(np.linalg.norm(av_col - rq * bv_col)) if math.isfinite(rq) else float("inf"))
        order = np.argsort(np.asarray(rayleighs, dtype=np.float64))
        rayleigh_array = np.asarray(rayleighs, dtype=np.float64)[order]
        residual_array = np.asarray(residuals, dtype=np.float64)[order]
        vecs = vecs[:, order]
        worst_vec = vecs[:, 0]
        av = np.asarray(backend_handle.neg_mv(worst_vec), dtype=np.float64)
        bv = np.asarray(backend_handle.abs_mv(worst_vec), dtype=np.float64)
        denominator = float(worst_vec @ bv)
        rayleigh = float((worst_vec @ av) / denominator) if abs(denominator) > float(zero_eps) else None
        lambda_min = rayleigh
        residual = float(np.linalg.norm(av - float(lambda_min) * bv)) if lambda_min is not None else None
        shell, shell_mass = _shell_localization(worst_vec, profile, zero_eps)
        iteration_count = int(len(lambda_history)) if hasattr(lambda_history, "__len__") else 0
        result_warnings = [str(item.message) for item in caught]
        if backend == "vulkan-matvec" and backend_handle.info.get("gpu_matvec_parity_ok") is not True:
            result_warnings.append("vulkan_matvec_cpu_parity_mismatch")
        return {
            "status": OK_STATUS,
            "lambda_min": lambda_min,
            "lambda_max": float(np.max(rayleigh_array)),
            "eigenvalues": [float(value) for value in rayleigh_array],
            "rayleigh_min": rayleigh,
            "worst_eigenvector_shell": shell,
            "worst_eigenvector_shell_mass_fraction": shell_mass,
            "iterations": iteration_count,
            "residual_norm": residual,
            "returned_residual_norms": [float(value) for value in residual_array],
            "elapsed_ms": float(1000.0 * (time.perf_counter() - started)),
            "dense_reconstruction_used": False,
            "iterative_solver": "scipy_lobpcg_linear_operator",
            "generalized_mass_shift": float(generalized_mass_shift),
            "warnings": result_warnings,
            **backend_handle.info,
        }
    except Exception as exc:  # noqa: BLE001
        return {
            "status": PARTIAL_STATUS,
            "lambda_min": None,
            "lambda_max": None,
            "worst_eigenvector_shell": None,
            "worst_eigenvector_shell_mass_fraction": None,
            "iterations": 0,
            "residual_norm": None,
            "elapsed_ms": float(1000.0 * (time.perf_counter() - started)),
            "dense_reconstruction_used": False,
            "iterative_solver": "scipy_lobpcg_linear_operator",
            "generalized_mass_shift": float(generalized_mass_shift),
            "gpu_matvec_parity_ok": None,
            "gpu_matvec_max_abs_error_abs": None,
            "gpu_matvec_max_abs_error_neg": None,
            "vulkan_icd": None,
            "icd_probe_errors": None,
            "block_matvec_enabled": False,
            "block_matvec_backend": None,
            "gpu_block_matvec_parity_ok": None,
            "gpu_block_matvec_max_abs_error_abs": None,
            "gpu_block_matvec_max_abs_error_neg": None,
            "warnings": [f"iterative_generalized_failed: {type(exc).__name__}: {exc}"],
        }
    finally:
        if backend_handle is not None:
            backend_handle.close()


def _dense_oracle(profile: MatrixFreeKNProfile, shell_n: int, zero_eps: float, limit: int) -> dict[str, Any] | None:
    if int(shell_n) > int(limit):
        return None
    dense = dense_parity_adapter(profile, zero_eps=zero_eps)
    return {
        "status": dense.get("status"),
        "lambda_min": dense.get("lambda_min"),
        "lambda_max": dense.get("lambda_max"),
        "l_abs_positive_rank": dense.get("l_abs_positive_rank"),
        "worst_eigenvector_shell": dense.get("worst_eigenvector_shell"),
        "worst_eigenvector_shell_mass_fraction": dense.get("worst_eigenvector_shell_mass_fraction"),
        "warnings": dense.get("warnings", []),
    }


def _evaluate(
    triads: list[Any],
    probability: np.ndarray,
    shell_levels: np.ndarray,
    profile_id: str,
    shell_n: int,
    backend: str,
    zero_eps: float,
    high_shell_cutoff: float,
    r0: float,
    high_shell_eta: float,
    d0: float,
    parity_tol: float,
    lobpcg_tol: float,
    lobpcg_maxiter: int,
    block_size: int,
    generalized_mass_shift: float,
    dense_oracle_shell_limit: int,
    gpu_checks: int,
) -> dict[str, Any]:
    profile = build_profile(
        triads=triads,
        probability=probability,
        mode_count=int(len(probability)),
        zero_eps=zero_eps,
        shell_levels=shell_levels,
        profile_id=profile_id,
    )
    iterative = _iterative_generalized(
        profile=profile,
        backend=backend,
        zero_eps=zero_eps,
        lobpcg_tol=lobpcg_tol,
        lobpcg_maxiter=lobpcg_maxiter,
        block_size=block_size,
        generalized_mass_shift=generalized_mass_shift,
        gpu_checks=gpu_checks,
    )
    dense = _dense_oracle(profile, shell_n=shell_n, zero_eps=zero_eps, limit=dense_oracle_shell_limit)
    dense_lambda = dense.get("lambda_min") if dense is not None else None
    iterative_lambda = iterative.get("lambda_min")
    absolute_error = None
    relative_error = None
    if isinstance(dense_lambda, (int, float)) and isinstance(iterative_lambda, (int, float)):
        absolute_error = float(abs(float(iterative_lambda) - float(dense_lambda)))
        relative_error = float(absolute_error / max(abs(float(dense_lambda)), 1.0e-12))

    metrics = _profile_metrics(probability, shell_levels, zero_eps, high_shell_cutoff)
    iterative_branch_input = {**metrics, "lambda_min_kn_a": iterative_lambda, "status": iterative["status"]}
    iterative_branch = _branch(iterative_branch_input, c0=0.25, r0=r0, high_shell_eta=high_shell_eta, d0=d0)
    dense_branch = None
    branch_agrees = None
    shell_agrees = None
    if dense is not None:
        dense_branch_input = {**metrics, "lambda_min_kn_a": dense_lambda, "status": dense["status"]}
        dense_branch = _branch(dense_branch_input, c0=0.25, r0=r0, high_shell_eta=high_shell_eta, d0=d0)
        branch_agrees = dense_branch == iterative_branch
        shell_agrees = dense.get("worst_eigenvector_shell") == iterative.get("worst_eigenvector_shell")

    eigen_agrees = bool(
        absolute_error is not None
        and relative_error is not None
        and (absolute_error <= float(parity_tol) or relative_error <= float(parity_tol))
    )
    dense_parity_ok = dense is None or bool(
        dense.get("status") == OK_STATUS
        and iterative.get("status") == OK_STATUS
        and eigen_agrees
        and branch_agrees is True
        and (
            shell_agrees is True
            or (
                isinstance(dense_lambda, (int, float))
                and isinstance(iterative_lambda, (int, float))
                and abs(float(dense_lambda)) <= float(parity_tol)
                and abs(float(iterative_lambda)) <= float(parity_tol)
            )
        )
    )
    gpu_parity_ok = backend != "vulkan-matvec" or iterative.get("gpu_matvec_parity_ok") is True
    parity_ok = bool(iterative.get("status") == OK_STATUS and dense_parity_ok and gpu_parity_ok)
    return {
        "profile_id": profile_id,
        "status": OK_STATUS if parity_ok else PARTIAL_STATUS,
        "candidate_only": True,
        "fail_closed": True,
        "kn_backend": backend,
        "gpu_kn_authority": False,
        "edge_count": int(len(profile.weights_abs)),
        "dense_oracle_used": dense is not None,
        "dense_reconstruction_used": False,
        "iterative_solver": iterative.get("iterative_solver"),
        "generalized_mass_shift": iterative.get("generalized_mass_shift"),
        "lambda_min_dense_cpu": dense_lambda,
        "lambda_min_iterative": iterative_lambda,
        "lambda_max_iterative": iterative.get("lambda_max"),
        "rayleigh_min_iterative": iterative.get("rayleigh_min"),
        "absolute_error_vs_dense": absolute_error,
        "relative_error_vs_dense": relative_error,
        "branch_classification_dense_cpu": dense_branch,
        "branch_classification_iterative": iterative_branch,
        "branch_classification_agrees": branch_agrees,
        "eigenvector_localization_degenerate": bool(
            dense is not None
            and shell_agrees is False
            and isinstance(dense_lambda, (int, float))
            and isinstance(iterative_lambda, (int, float))
            and abs(float(dense_lambda)) <= float(parity_tol)
            and abs(float(iterative_lambda)) <= float(parity_tol)
        ),
        "worst_eigenvector_shell_dense_cpu": dense.get("worst_eigenvector_shell") if dense is not None else None,
        "worst_eigenvector_shell_iterative": iterative.get("worst_eigenvector_shell"),
        "worst_eigenvector_shell_mass_dense_cpu": (
            dense.get("worst_eigenvector_shell_mass_fraction") if dense is not None else None
        ),
        "worst_eigenvector_shell_mass_iterative": iterative.get("worst_eigenvector_shell_mass_fraction"),
        "worst_eigenvector_shell_mass_agrees": shell_agrees,
        "iterations": iterative.get("iterations"),
        "residual_norm": iterative.get("residual_norm"),
        "elapsed_ms": iterative.get("elapsed_ms"),
        "gpu_matvec_max_abs_error_abs": iterative.get("gpu_matvec_max_abs_error_abs"),
        "gpu_matvec_max_abs_error_neg": iterative.get("gpu_matvec_max_abs_error_neg"),
        "gpu_matvec_parity_ok": iterative.get("gpu_matvec_parity_ok"),
        "vulkan_icd": iterative.get("vulkan_icd"),
        "icd_probe_errors": iterative.get("icd_probe_errors"),
        "block_matvec_enabled": iterative.get("block_matvec_enabled"),
        "block_matvec_backend": iterative.get("block_matvec_backend"),
        "gpu_block_matvec_parity_ok": iterative.get("gpu_block_matvec_parity_ok"),
        "gpu_block_matvec_max_abs_error_abs": iterative.get("gpu_block_matvec_max_abs_error_abs"),
        "gpu_block_matvec_max_abs_error_neg": iterative.get("gpu_block_matvec_max_abs_error_neg"),
        "parity_ok": parity_ok,
        "warnings": list(iterative.get("warnings", [])) + ([] if dense is None else list(dense.get("warnings", []))),
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
    lobpcg_tol: float,
    lobpcg_maxiter: int,
    block_size: int,
    generalized_mass_shift: float,
    dense_oracle_shell_limit: int,
    gpu_checks: int,
    max_profiles_per_row: int,
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
        "dense_reconstruction_used": False,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        shell_modes: list[ModeRecord] = _cube_modes(spectrum, shell_n=shell_n, zero_eps=zero_eps)
        triads, _frame_metrics = _build_frame_surface(shell_modes, zero_eps=zero_eps, triad_sample_limit=8)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"kn_iterative_eig_scan_error: {exc}"]
        return row

    row["selected_mode_count"] = int(len(shell_modes))
    row["triad_count"] = int(len(triads))
    row["dense_oracle_used"] = bool(int(shell_n) <= int(dense_oracle_shell_limit))
    if len(shell_modes) < 3 or not triads:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_insufficient_modes"]
        row["profile_count"] = 0
        row["parity_ok_count"] = 0
        row["parity_mismatch_count"] = 0
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
            if int(max_profiles_per_row) > 0 and len(evaluated) >= int(max_profiles_per_row):
                break
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
                    shell_n=shell_n,
                    backend=backend,
                    zero_eps=zero_eps,
                    high_shell_cutoff=high_shell_cutoff,
                    r0=r0,
                    high_shell_eta=high_shell_eta,
                    d0=d0,
                    parity_tol=parity_tol,
                    lobpcg_tol=lobpcg_tol,
                    lobpcg_maxiter=lobpcg_maxiter,
                    block_size=block_size,
                    generalized_mass_shift=generalized_mass_shift,
                    dense_oracle_shell_limit=dense_oracle_shell_limit,
                    gpu_checks=gpu_checks,
                )
            )
        if int(max_profiles_per_row) > 0 and len(evaluated) >= int(max_profiles_per_row):
            break
    ok_profiles = [item for item in evaluated if item.get("parity_ok") is True]
    best = min(
        (item for item in evaluated if isinstance(item.get("lambda_min_iterative"), (int, float))),
        key=lambda item: float(item["lambda_min_iterative"]),
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
    oracle_profiles = sum(
        int(row.get("profile_count", 0)) for row in rows if row.get("dense_oracle_used") is True
    )
    no_oracle_profiles = max(0, int(total_profiles - oracle_profiles))
    return {
        "processed_rows": int(len(rows)),
        "ok_rows": int(sum(1 for row in rows if row.get("status") == OK_STATUS)),
        "partial_rows": int(sum(1 for row in rows if row.get("status") == PARTIAL_STATUS)),
        "error_rows": int(sum(1 for row in rows if row.get("status") == ERROR_STATUS)),
        "kn_backend": backend,
        "sampled_profile_count": int(total_profiles),
        "dense_oracle_profile_count": int(oracle_profiles),
        "no_dense_oracle_profile_count": int(no_oracle_profiles),
        "parity_ok_count": int(parity_ok),
        "parity_mismatch_count": int(mismatches),
        "all_small_shell_parity_passed": bool(oracle_profiles > 0 and mismatches == 0),
        "n4_plus_without_dense_reconstruction": bool(
            any(int(row.get("shell", 0)) >= 4 and row.get("dense_reconstruction_used") is False for row in rows)
        ),
        "gpu_kn_authority": False,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "kn_iterative_status": "fail-closed" if mismatches else "candidate-iterative-parity",
        "dense_eigensolve_scope": "small_shell_oracle_only",
        "dense_reconstruction_used_by_iterative_lane": False,
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells if args.shells is not None else list(DEFAULT_SHELLS))
    seeds = [int(seed) for seed in (args.seeds if args.seeds is not None else list(DEFAULT_SEEDS))]
    warnings_list: list[str] = []
    if args.kn_backend == "vulkan-matvec":
        warnings_list.append("vulkan_matvec_backend_non_authoritative_gpu_kn_authority_false")
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings_list)
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
            lobpcg_tol=float(args.lobpcg_tol),
            lobpcg_maxiter=int(args.lobpcg_maxiter),
            block_size=int(args.block_size),
            generalized_mass_shift=float(args.generalized_mass_shift),
            dense_oracle_shell_limit=int(args.dense_oracle_shell_limit),
            gpu_checks=int(args.gpu_matvec_checks),
            max_profiles_per_row=int(args.max_profiles_per_row),
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
            "frame_limit": int(args.frame_limit),
            "zero_eps": float(args.zero_eps),
            "sample_count": int(args.sample_count),
            "mix_count": int(args.mix_count),
            "profile_sample_limit": int(args.profile_sample_limit),
            "max_profiles_per_row": int(args.max_profiles_per_row),
            "seeds": seeds,
            "shells": [int(shell) for shell in shells],
            "d0": float(args.d0),
            "r0": float(args.r0),
            "high_shell_cutoff": float(args.high_shell_cutoff),
            "high_shell_eta": float(args.high_shell_eta),
            "parity_tol": float(args.parity_tol),
            "lobpcg_tol": float(args.lobpcg_tol),
            "lobpcg_maxiter": int(args.lobpcg_maxiter),
            "block_size": int(args.block_size),
            "generalized_mass_shift": float(args.generalized_mass_shift),
            "dense_oracle_shell_limit": int(args.dense_oracle_shell_limit),
            "gpu_matvec_checks": int(args.gpu_matvec_checks),
        },
        "status": ERROR_STATUS if any(row.get("status") == ERROR_STATUS for row in rows) else (
            OK_STATUS if all(row.get("status") == OK_STATUS for row in rows) else PARTIAL_STATUS
        ),
        "rows": rows,
        "aggregate": _aggregate(rows, backend=args.kn_backend),
        "warnings": warnings_list,
        "errors": [error for row in rows for error in row.get("errors", [])],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, pretty=args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0 if payload["status"] != ERROR_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
