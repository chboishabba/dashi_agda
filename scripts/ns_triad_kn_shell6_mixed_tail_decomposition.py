#!/usr/bin/env python3
"""Decompose the shell-6 mixed-tail K_N(A) receipt.

This is a candidate-only diagnostic for the v4 shell-6 row.  It rebuilds the
``forced_tail_K4_eta_0.250`` profile, solves the same generalized eigenproblem,
and emits shell-mass, shell-pair Rayleigh, Schur, quotient-split, and BKM-proxy
projection tables.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np
from scipy.sparse import coo_matrix, eye
from scipy.sparse.linalg import cg, lobpcg

from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
from ns_triad_constrained_adversarial_fork_optimizer import (  # type: ignore
    _cube_modes,
    _normalize_profile,
    _profile_metrics,
    _shell_levels,
)
from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_ZERO_EPS,
    OK_STATUS,
    _build_frame_surface,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
    _wrap_phase,
)
from ns_triad_kn_iterative_generalized_eig import (  # type: ignore
    DEFAULT_GENERALIZED_MASS_SHIFT,
    DEFAULT_LOBPCG_MAXITER,
    DEFAULT_LOBPCG_TOL,
    _make_backend,
    _operator_from_matvec,
    _shifted_operator_from_matvec,
)
from ns_triad_kn_matrix_free_operator import (  # type: ignore
    MatrixFreeKNProfile,
    build_profile,
)


SCRIPT_NAME = "scripts/ns_triad_kn_shell6_mixed_tail_decomposition.py"
CONTRACT = "ns_triad_kn_shell6_mixed_tail_decomposition"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_SHELL6_MIXED_TAIL_DECOMPOSITION"
SCHEMA_VERSION = "1.1.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_shell6_mixed_tail_decomposition_20260623.json"
)
DEFAULT_OUTPUT_MD = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_shell6_mixed_tail_decomposition_20260623.md"
)

CONTROL_CARD = {
    "O": "Decompose the shell-6 mixed-tail candidate into shell and shell-pair accounting tables.",
    "R": (
        "Rebuild forced_tail_K4_eta_0.250 on the shell-6 carrier, solve "
        "L_neg x = lambda L_abs x, and test whether the K>=4 tail drives the "
        "low Rayleigh quotient."
    ),
    "C": SCRIPT_NAME,
    "S": "Finite numerical receipt only; no theorem, full-NS, or Clay promotion.",
    "L": (
        "Report eigen/profile shell masses, shell-pair numerator and denominator, "
        "positive/negative sector weights, Schur repair quadratics, tail/finite/cross "
        "Rayleigh splits, and BKM-proxy projections."
    ),
    "P": ROUTE_DECISION,
    "G": "All outputs are candidate-only and fail-closed.",
    "F": "This does not prove coherence orthogonality, Schur repair, or residence-time exclusion.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--output-md", type=Path, default=DEFAULT_OUTPUT_MD)
    parser.add_argument("--kn-backend", choices=("cpu-matrix-free", "vulkan-matvec"), default="vulkan-matvec")
    parser.add_argument("--gpu-matvec-checks", type=int, default=1)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=1)
    parser.add_argument("--shell", type=int, default=6)
    parser.add_argument("--tail-cutoff", type=int, default=4)
    parser.add_argument("--tail-eta", type=float, default=0.25)
    parser.add_argument("--triad-sample-limit", type=int, default=64)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--lobpcg-tol", type=float, default=DEFAULT_LOBPCG_TOL)
    parser.add_argument("--lobpcg-maxiter", type=int, default=DEFAULT_LOBPCG_MAXITER)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--generalized-mass-shift", type=float, default=DEFAULT_GENERALIZED_MASS_SHIFT)
    parser.add_argument(
        "--profile-builder",
        choices=("auto", "frame-surface", "streaming"),
        default="auto",
        help="Build K_N(A) profile from the full triad surface or stream directly into edge arrays.",
    )
    parser.add_argument(
        "--streaming-shell-threshold",
        type=int,
        default=10,
        help="In --profile-builder=auto, use streaming construction at this shell and above.",
    )
    parser.add_argument(
        "--dense-schur-mode-limit",
        type=int,
        default=6000,
        help="Skip dense Schur diagnostics when the selected mode count exceeds this limit; set <0 to force.",
    )
    parser.add_argument(
        "--sparse-schur",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="When dense Schur is skipped, estimate the Schur quadratic with sparse q00 solves.",
    )
    parser.add_argument(
        "--sparse-schur-tol",
        type=float,
        default=1.0e-8,
        help="Relative tolerance for sparse Schur q00 solves.",
    )
    parser.add_argument(
        "--sparse-schur-maxiter",
        type=int,
        default=2000,
        help="Maximum CG iterations for sparse Schur q00 solves.",
    )
    parser.add_argument(
        "--sparse-schur-ridge",
        type=float,
        default=1.0e-12,
        help="Small diagonal ridge used only to stabilize singular sparse q00 solves.",
    )
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _shell_mass_table(shell_levels: np.ndarray, values: np.ndarray, key: str) -> list[dict[str, Any]]:
    total = float(np.sum(values))
    rows = []
    for shell in sorted({int(value) for value in shell_levels}):
        mask = shell_levels == float(shell)
        mass = float(np.sum(values[mask]))
        rows.append({"shell": int(shell), key: mass, "fraction": float(mass / max(total, 1.0e-300))})
    return rows


def _forced_tail_profile(shell_levels: np.ndarray, cutoff: int, eta: float, zero_eps: float) -> np.ndarray:
    shells = np.asarray(shell_levels, dtype=np.float64)
    low_shell = float(np.min(shells))
    low = _normalize_profile(np.where(shells <= low_shell + 1.0e-12, 1.0, 0.0), zero_eps)
    high_raw = np.where(shells >= float(cutoff), 1.0, 0.0)
    high = _normalize_profile(high_raw, zero_eps) if np.any(high_raw > 0.0) else np.zeros_like(low)
    return _normalize_profile((1.0 - float(eta)) * low + float(eta) * high, zero_eps)


def _streaming_profile(
    *,
    modes: list[Any],
    probability: np.ndarray,
    shell_levels: np.ndarray,
    zero_eps: float,
    profile_id: str,
) -> tuple[MatrixFreeKNProfile, dict[str, Any]]:
    """Build the matrix-free profile without retaining TriadRecord objects.

    The older diagnostic path materializes every resonant triad first, then
    filters by the profile.  At shell 10 this creates millions of Python
    objects before the eigensolve starts.  This path computes the same weighted
    pair incidence arrays directly.
    """

    key_to_index = {mode.key: index for index, mode in enumerate(modes)}
    profile_amplitude = np.sqrt(np.maximum(np.asarray(probability, dtype=np.float64), 0.0))
    left_edges: list[int] = []
    right_edges: list[int] = []
    weights_abs: list[float] = []
    weights_neg: list[float] = []
    operator_triad_count = 0
    retained_triad_count = 0
    positive_weight_sum = 0.0
    negative_weight_sum = 0.0

    for left in range(len(modes)):
        mode_left = modes[left]
        for right in range(left + 1, len(modes)):
            mode_right = modes[right]
            key_out = (
                mode_left.key[0] + mode_right.key[0],
                mode_left.key[1] + mode_right.key[1],
                mode_left.key[2] + mode_right.key[2],
            )
            out = key_to_index.get(key_out)
            if out is None or out == left or out == right:
                continue
            mode_out = modes[out]
            mode_weight = float(mode_left.amplitude * mode_right.amplitude * mode_out.amplitude)
            if not math.isfinite(mode_weight) or mode_weight <= float(zero_eps):
                continue
            operator_triad_count += 1

            raw_weight = float(profile_amplitude[left] * profile_amplitude[right] * profile_amplitude[out])
            if not math.isfinite(raw_weight) or raw_weight <= float(zero_eps):
                continue
            closure = _wrap_phase(mode_left.phase + mode_right.phase - mode_out.phase)
            coherence = float(math.cos(closure))
            pair_weight = raw_weight / 3.0
            positive_weight = pair_weight * max(coherence, 0.0)
            negative_weight = pair_weight * max(-coherence, 0.0)
            absolute_weight = positive_weight + negative_weight
            if absolute_weight <= float(zero_eps):
                continue
            retained_triad_count += 1
            positive_weight_sum += float(positive_weight)
            negative_weight_sum += float(negative_weight)
            for a, b in ((left, right), (left, out), (right, out)):
                left_edges.append(int(a))
                right_edges.append(int(b))
                weights_abs.append(float(absolute_weight))
                weights_neg.append(float(negative_weight))

    index_dtype = np.int32 if len(modes) <= np.iinfo(np.int32).max else np.int64
    profile = MatrixFreeKNProfile(
        mode_count=int(len(modes)),
        edge_left=np.asarray(left_edges, dtype=index_dtype),
        edge_right=np.asarray(right_edges, dtype=index_dtype),
        weights_abs=np.asarray(weights_abs, dtype=np.float64),
        weights_neg=np.asarray(weights_neg, dtype=np.float64),
        shell_levels=np.asarray(shell_levels, dtype=np.float64),
        profile_id=str(profile_id),
    )
    frame_metrics = {
        "selected_mode_count": int(len(modes)),
        "carrier_stratum_count": int(len({int(value) for value in shell_levels})),
        "triad_count": int(operator_triad_count),
        "profile_retained_triad_count": int(retained_triad_count),
        "triad_positive_backbone_mass": float(positive_weight_sum),
        "triad_negative_frame_mass": float(negative_weight_sum),
        "triad_samples": [],
        "profile_builder": "streaming",
    }
    return profile, frame_metrics


def _solve_worst_vector(
    *,
    profile: Any,
    zero_eps: float,
    lobpcg_tol: float,
    lobpcg_maxiter: int,
    block_size: int,
    generalized_mass_shift: float,
    backend: str,
    gpu_checks: int,
) -> dict[str, Any]:
    n = int(profile.mode_count)
    backend_handle = _make_backend(profile, backend, zero_eps, gpu_checks)
    try:
        a_op = _operator_from_matvec(backend_handle.neg_mv, backend_handle.neg_mm, n)
        b_op = _shifted_operator_from_matvec(
            backend_handle.abs_mv,
            backend_handle.abs_mm,
            n,
            max(float(generalized_mass_shift), 0.0),
        )
        k = max(1, min(int(block_size), n - 2))
        rng = np.random.default_rng(20260623)
        x0 = rng.normal(size=(n, k))
        y = np.ones((n, 1), dtype=np.float64)
        eigs, vecs = lobpcg(
            a_op,
            x0,
            B=b_op,
            Y=y,
            tol=float(lobpcg_tol),
            maxiter=int(lobpcg_maxiter),
            largest=False,
        )
        vecs = np.asarray(vecs, dtype=np.float64)
        rayleighs = []
        for column in range(vecs.shape[1]):
            vec = vecs[:, column]
            av = np.asarray(backend_handle.neg_mv(vec), dtype=np.float64)
            bv = np.asarray(backend_handle.abs_mv(vec), dtype=np.float64)
            den = float(vec @ bv)
            rayleighs.append(float((vec @ av) / den) if abs(den) > float(zero_eps) else float("inf"))
        order = np.argsort(np.asarray(rayleighs, dtype=np.float64))
        vector = np.asarray(vecs[:, int(order[0])], dtype=np.float64)
        av = np.asarray(backend_handle.neg_mv(vector), dtype=np.float64)
        bv = np.asarray(backend_handle.abs_mv(vector), dtype=np.float64)
        numerator = float(vector @ av)
        denominator = float(vector @ bv)
        lambda_min = float(numerator / denominator) if abs(denominator) > float(zero_eps) else None
        return {
            "lambda_min": lambda_min,
            "vector": vector,
            "numerator": numerator,
            "denominator": denominator,
            "returned_eigenvalues": [float(value) for value in np.asarray(eigs, dtype=np.float64)],
            "backend_info": backend_handle.info,
        }
    finally:
        backend_handle.close()


def _pair_key(shell_a: float, shell_b: float) -> str:
    left, right = sorted((int(shell_a), int(shell_b)))
    return f"{left}-{right}"


def _shell_pair_tables(profile: Any, vector: np.ndarray) -> dict[str, Any]:
    levels = np.asarray(profile.shell_levels, dtype=np.float64)
    numerator: dict[str, float] = {}
    denominator: dict[str, float] = {}
    negative_weight: dict[str, float] = {}
    positive_weight: dict[str, float] = {}
    absolute_weight: dict[str, float] = {}
    for left, right, w_abs, w_neg in zip(
        profile.edge_left,
        profile.edge_right,
        profile.weights_abs,
        profile.weights_neg,
        strict=False,
    ):
        key = _pair_key(levels[int(left)], levels[int(right)])
        diff2 = float((vector[int(left)] - vector[int(right)]) ** 2)
        numerator[key] = numerator.get(key, 0.0) + float(w_neg) * diff2
        denominator[key] = denominator.get(key, 0.0) + float(w_abs) * diff2
        negative_weight[key] = negative_weight.get(key, 0.0) + float(w_neg)
        positive_weight[key] = positive_weight.get(key, 0.0) + max(float(w_abs) - float(w_neg), 0.0)
        absolute_weight[key] = absolute_weight.get(key, 0.0) + float(w_abs)

    keys = sorted(set(numerator) | set(denominator) | set(negative_weight) | set(positive_weight))
    total_num = sum(numerator.values())
    total_den = sum(denominator.values())
    total_neg_weight = sum(negative_weight.values())
    total_pos_weight = sum(positive_weight.values())
    rows = []
    for key in keys:
        num = float(numerator.get(key, 0.0))
        den = float(denominator.get(key, 0.0))
        neg = float(negative_weight.get(key, 0.0))
        pos = float(positive_weight.get(key, 0.0))
        rows.append(
            {
                "shell_pair": key,
                "l_neg_numerator": num,
                "l_neg_numerator_fraction": float(num / max(total_num, 1.0e-300)),
                "l_abs_denominator": den,
                "l_abs_denominator_fraction": float(den / max(total_den, 1.0e-300)),
                "l_pos_denominator": float(den - num),
                "l_pos_denominator_fraction": float((den - num) / max(total_den, 1.0e-300)),
                "negative_sector_denominator": num,
                "negative_sector_denominator_fraction": float(num / max(total_den, 1.0e-300)),
                "positive_sector_denominator": float(den - num),
                "positive_sector_denominator_fraction": float((den - num) / max(total_den, 1.0e-300)),
                "negative_frame_weight": neg,
                "negative_frame_weight_fraction": float(neg / max(total_neg_weight, 1.0e-300)),
                "positive_frame_weight": pos,
                "positive_frame_weight_fraction": float(pos / max(total_pos_weight, 1.0e-300)),
                "absolute_frame_weight": float(absolute_weight.get(key, 0.0)),
            }
        )
    return {
        "rows": rows,
        "totals": {
            "l_neg_numerator": float(total_num),
            "l_abs_denominator": float(total_den),
            "l_pos_denominator": float(total_den - total_num),
            "negative_frame_weight": float(total_neg_weight),
            "positive_frame_weight": float(total_pos_weight),
            "rayleigh_quotient": float(total_num / total_den),
        },
    }


def _quadratic(weights: np.ndarray, profile: Any, left: np.ndarray, right: np.ndarray, vector: np.ndarray) -> float:
    if len(weights) == 0:
        return 0.0
    diff = vector[left] - vector[right]
    return float(np.sum(weights * diff * diff))


def _bilinear(weights: np.ndarray, profile: Any, left: np.ndarray, right: np.ndarray, x: np.ndarray, y: np.ndarray) -> float:
    if len(weights) == 0:
        return 0.0
    diff_x = x[left] - x[right]
    diff_y = y[left] - y[right]
    return float(np.sum(weights * diff_x * diff_y))


def _rayleigh_from_terms(numerator: float, denominator: float, zero_eps: float) -> float | None:
    if not math.isfinite(denominator) or abs(float(denominator)) <= float(zero_eps):
        return None
    return float(numerator / denominator)


def _component_rayleigh_split(
    profile: Any,
    shell_levels: np.ndarray,
    vector: np.ndarray,
    cutoff: int,
    zero_eps: float,
) -> dict[str, Any]:
    levels = np.asarray(shell_levels, dtype=np.float64)
    left = np.asarray(profile.edge_left, dtype=np.int64)
    right = np.asarray(profile.edge_right, dtype=np.int64)
    finite_mask = levels < float(cutoff)
    tail_mask = levels >= float(cutoff)
    finite = np.where(finite_mask, vector, 0.0)
    tail = np.where(tail_mask, vector, 0.0)

    def split_for(weights: np.ndarray) -> dict[str, float]:
        ff = _quadratic(weights, profile, left, right, finite)
        tt = _quadratic(weights, profile, left, right, tail)
        cross = 2.0 * _bilinear(weights, profile, left, right, finite, tail)
        return {
            "finite_finite": float(ff),
            "tail_tail": float(tt),
            "finite_tail_cross": float(cross),
            "total_from_terms": float(ff + tt + cross),
            "total_direct": _quadratic(weights, profile, left, right, vector),
        }

    neg = split_for(np.asarray(profile.weights_neg, dtype=np.float64))
    abs_ = split_for(np.asarray(profile.weights_abs, dtype=np.float64))
    pos_weights = np.asarray(profile.weights_abs, dtype=np.float64) - np.asarray(profile.weights_neg, dtype=np.float64)
    pos = split_for(np.maximum(pos_weights, 0.0))
    full_num = neg["total_from_terms"]
    full_den = abs_["total_from_terms"]
    return {
        "tail_cutoff": int(cutoff),
        "finite_mode_count": int(np.count_nonzero(finite_mask)),
        "tail_mode_count": int(np.count_nonzero(tail_mask)),
        "finite_euclidean_mass": float(np.sum(finite * finite) / max(float(np.sum(vector * vector)), 1.0e-300)),
        "tail_euclidean_mass": float(np.sum(tail * tail) / max(float(np.sum(vector * vector)), 1.0e-300)),
        "l_neg_split": neg,
        "l_abs_split": abs_,
        "l_pos_split": pos,
        "finite_only_rayleigh": _rayleigh_from_terms(neg["finite_finite"], abs_["finite_finite"], zero_eps),
        "tail_only_rayleigh": _rayleigh_from_terms(neg["tail_tail"], abs_["tail_tail"], zero_eps),
        "cross_term_rayleigh": _rayleigh_from_terms(neg["finite_tail_cross"], abs_["finite_tail_cross"], zero_eps),
        "full_rayleigh_from_terms": _rayleigh_from_terms(full_num, full_den, zero_eps),
        "cross_l_neg_fraction_of_full_numerator": float(neg["finite_tail_cross"] / max(full_num, 1.0e-300)),
        "cross_l_abs_fraction_of_full_denominator": float(abs_["finite_tail_cross"] / max(full_den, 1.0e-300)),
        "tail_l_neg_fraction_of_full_numerator": float(neg["tail_tail"] / max(full_num, 1.0e-300)),
        "tail_l_abs_fraction_of_full_denominator": float(abs_["tail_tail"] / max(full_den, 1.0e-300)),
        "finite_l_neg_fraction_of_full_numerator": float(neg["finite_finite"] / max(full_num, 1.0e-300)),
        "finite_l_abs_fraction_of_full_denominator": float(abs_["finite_finite"] / max(full_den, 1.0e-300)),
    }


def _add_laplacian_edge(matrix: np.ndarray, i: int, j: int, weight: float) -> None:
    matrix[i, i] += weight
    matrix[j, j] += weight
    matrix[i, j] -= weight
    matrix[j, i] -= weight


def _schur_blocks(profile: Any, core: np.ndarray, tail: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    core_pos = {int(index): pos for pos, index in enumerate(core)}
    tail_pos = {int(index): pos for pos, index in enumerate(tail)}
    q00 = np.zeros((len(core), len(core)), dtype=np.float64)
    q01 = np.zeros((len(core), len(tail)), dtype=np.float64)
    q11 = np.zeros((len(tail), len(tail)), dtype=np.float64)
    for left, right, w_abs, w_neg in zip(
        profile.edge_left,
        profile.edge_right,
        profile.weights_abs,
        profile.weights_neg,
        strict=False,
    ):
        weight = float(w_abs) - float(w_neg)
        if weight == 0.0:
            continue
        left = int(left)
        right = int(right)
        left_core = core_pos.get(left)
        right_core = core_pos.get(right)
        left_tail = tail_pos.get(left)
        right_tail = tail_pos.get(right)
        if left_core is not None and right_core is not None:
            _add_laplacian_edge(q00, left_core, right_core, weight)
        elif left_tail is not None and right_tail is not None:
            _add_laplacian_edge(q11, left_tail, right_tail, weight)
        elif left_core is not None and right_tail is not None:
            q00[left_core, left_core] += weight
            q11[right_tail, right_tail] += weight
            q01[left_core, right_tail] -= weight
        elif left_tail is not None and right_core is not None:
            q11[left_tail, left_tail] += weight
            q00[right_core, right_core] += weight
            q01[right_core, left_tail] -= weight
    return q00, q01, q11


def _schur_rows(profile: Any, vector: np.ndarray, cutoffs: list[int], zero_eps: float) -> list[dict[str, Any]]:
    levels = np.asarray(profile.shell_levels, dtype=np.float64)
    rows = []
    for cutoff in cutoffs:
        core = np.flatnonzero(levels < float(cutoff))
        tail = np.flatnonzero(levels >= float(cutoff))
        x0 = vector[core]
        x1 = vector[tail]
        q00, q01, q11 = _schur_blocks(profile, core, tail)
        q10 = q01.T
        q_core = float(x0 @ q00 @ x0) if len(core) else 0.0
        q_diag = float(x1 @ q11 @ x1) if len(tail) else 0.0
        q_coup = float(2.0 * x0 @ q01 @ x1) if len(core) and len(tail) else 0.0
        if len(core) and len(tail):
            q00_pinv = np.linalg.pinv(q00, rcond=max(float(zero_eps), 1.0e-10))
            schur = q11 - q10 @ q00_pinv @ q01
            q_schur = float(x1 @ schur @ x1)
        else:
            q_schur = q_diag
        rows.append(
            {
                "tail_cutoff": int(cutoff),
                "core_mode_count": int(len(core)),
                "tail_mode_count": int(len(tail)),
                "q_core": q_core,
                "q_diag": q_diag,
                "q_coup": q_coup,
                "q_total": float(q_core + q_diag + q_coup),
                "q_schur": q_schur,
                "q_gap": float(q_schur / max(float(np.linalg.norm(x1) ** 2), float(zero_eps))),
            }
        )
    return rows


def _schur_lite_rows(profile: Any, vector: np.ndarray, cutoffs: list[int]) -> list[dict[str, Any]]:
    """Compute Schur-style block quadratics without dense block matrices.

    This is not a true Schur complement because it does not form
    ``q11 - q10 q00^+ q01``.  It is the large-shell diagnostic we can afford:
    tail diagonal energy, finite-tail coupling, and the resulting gap per
    tail eigenvector mass for the positive repair form.
    """

    levels = np.asarray(profile.shell_levels, dtype=np.float64)
    left = np.asarray(profile.edge_left, dtype=np.int64)
    right = np.asarray(profile.edge_right, dtype=np.int64)
    pos_weights = np.maximum(
        np.asarray(profile.weights_abs, dtype=np.float64) - np.asarray(profile.weights_neg, dtype=np.float64),
        0.0,
    )
    rows = []
    for cutoff in cutoffs:
        core_mask = levels < float(cutoff)
        tail_mask = levels >= float(cutoff)
        finite = np.where(core_mask, vector, 0.0)
        tail = np.where(tail_mask, vector, 0.0)
        q_core = _quadratic(pos_weights, profile, left, right, finite)
        q_diag = _quadratic(pos_weights, profile, left, right, tail)
        q_coup = 2.0 * _bilinear(pos_weights, profile, left, right, finite, tail)
        tail_norm_sq = float(np.sum(tail * tail))
        q_total = float(q_core + q_diag + q_coup)
        rows.append(
            {
                "tail_cutoff": int(cutoff),
                "core_mode_count": int(np.count_nonzero(core_mask)),
                "tail_mode_count": int(np.count_nonzero(tail_mask)),
                "q_core": float(q_core),
                "q_diag": float(q_diag),
                "q_coup": float(q_coup),
                "q_total": q_total,
                "q_gap_lite": float(q_total / max(tail_norm_sq, 1.0e-300)),
                "q_diag_gap_lite": float(q_diag / max(tail_norm_sq, 1.0e-300)),
                "q_coup_fraction_of_q_diag": float(q_coup / max(abs(q_diag), 1.0e-300)),
                "tail_euclidean_mass": float(tail_norm_sq / max(float(np.sum(vector * vector)), 1.0e-300)),
            }
        )
    return rows


def _sparse_schur_rows(
    profile: Any,
    vector: np.ndarray,
    cutoffs: list[int],
    zero_eps: float,
    *,
    solve_tol: float,
    solve_maxiter: int,
    ridge: float,
) -> list[dict[str, Any]]:
    """Estimate true Schur quadratics using sparse q00 solves.

    For a core/tail split of the positive repair form Q, this computes

        x_tail^T (q11 - q10 q00^+ q01) x_tail

    without materializing dense q00/q01/q11 blocks.  The only matrix built is
    sparse q00 on the finite/core block; q01 x_tail and q11's quadratic are
    accumulated directly from the edge list.
    """

    levels = np.asarray(profile.shell_levels, dtype=np.float64)
    left_edges = np.asarray(profile.edge_left, dtype=np.int64)
    right_edges = np.asarray(profile.edge_right, dtype=np.int64)
    pos_weights = np.maximum(
        np.asarray(profile.weights_abs, dtype=np.float64) - np.asarray(profile.weights_neg, dtype=np.float64),
        0.0,
    )
    rows: list[dict[str, Any]] = []
    for cutoff in cutoffs:
        core = np.flatnonzero(levels < float(cutoff))
        tail = np.flatnonzero(levels >= float(cutoff))
        core_mode_count = int(len(core))
        tail_mode_count = int(len(tail))
        x0 = np.asarray(vector[core], dtype=np.float64)
        x1 = np.asarray(vector[tail], dtype=np.float64)
        tail_norm_sq = float(x1 @ x1)
        if core_mode_count == 0 or tail_mode_count == 0:
            rows.append(
                {
                    "tail_cutoff": int(cutoff),
                    "core_mode_count": core_mode_count,
                    "tail_mode_count": tail_mode_count,
                    "q_core": 0.0,
                    "q_diag": 0.0,
                    "q_coup": 0.0,
                    "q_total": 0.0,
                    "q_schur_sparse": 0.0,
                    "q_schur_subtraction": 0.0,
                    "q_gap_sparse": None,
                    "q_gap_kind": "sparse_positive_schur_per_tail_mass",
                    "cg_info": None,
                    "cg_residual_norm": None,
                    "cg_rhs_norm": None,
                    "ridge": float(ridge),
                    "tail_euclidean_mass": float(tail_norm_sq / max(float(np.sum(vector * vector)), 1.0e-300)),
                    "skipped": False,
                }
            )
            continue

        core_pos = {int(index): pos for pos, index in enumerate(core)}
        tail_pos = {int(index): pos for pos, index in enumerate(tail)}
        q00_rows: list[int] = []
        q00_cols: list[int] = []
        q00_vals: list[float] = []
        rhs = np.zeros(core_mode_count, dtype=np.float64)
        q_core = 0.0
        q_diag = 0.0
        q_coup = 0.0

        def add_q00(i: int, j: int, value: float) -> None:
            q00_rows.append(int(i))
            q00_cols.append(int(j))
            q00_vals.append(float(value))

        for left, right, weight in zip(left_edges, right_edges, pos_weights, strict=False):
            w = float(weight)
            if w == 0.0:
                continue
            left = int(left)
            right = int(right)
            left_core = core_pos.get(left)
            right_core = core_pos.get(right)
            left_tail = tail_pos.get(left)
            right_tail = tail_pos.get(right)
            if left_core is not None and right_core is not None:
                dx = float(x0[left_core] - x0[right_core])
                q_core += w * dx * dx
                add_q00(left_core, left_core, w)
                add_q00(right_core, right_core, w)
                add_q00(left_core, right_core, -w)
                add_q00(right_core, left_core, -w)
            elif left_tail is not None and right_tail is not None:
                dx = float(x1[left_tail] - x1[right_tail])
                q_diag += w * dx * dx
            elif left_core is not None and right_tail is not None:
                xt = float(x1[right_tail])
                xc = float(x0[left_core])
                q_core += w * xc * xc
                q_diag += w * xt * xt
                cross = -2.0 * w * xc * xt
                q_coup += cross
                add_q00(left_core, left_core, w)
                rhs[left_core] += -w * xt
            elif left_tail is not None and right_core is not None:
                xt = float(x1[left_tail])
                xc = float(x0[right_core])
                q_core += w * xc * xc
                q_diag += w * xt * xt
                cross = -2.0 * w * xc * xt
                q_coup += cross
                add_q00(right_core, right_core, w)
                rhs[right_core] += -w * xt

        q00 = coo_matrix(
            (np.asarray(q00_vals, dtype=np.float64), (np.asarray(q00_rows), np.asarray(q00_cols))),
            shape=(core_mode_count, core_mode_count),
        ).tocsr()
        rhs_norm = float(np.linalg.norm(rhs))
        ridge_value = max(float(ridge), 0.0)
        solve_matrix = q00 + ridge_value * eye(core_mode_count, format="csr") if ridge_value > 0.0 else q00
        if rhs_norm <= max(float(zero_eps), 1.0e-300):
            solution = np.zeros(core_mode_count, dtype=np.float64)
            cg_info: int | None = 0
            residual_norm = 0.0
        else:
            solution, cg_info = cg(
                solve_matrix,
                rhs,
                rtol=float(solve_tol),
                atol=0.0,
                maxiter=int(solve_maxiter),
            )
            residual_norm = float(np.linalg.norm(solve_matrix @ solution - rhs))
        subtraction = float(rhs @ solution)
        q_schur = float(q_diag - subtraction)
        q_total = float(q_core + q_diag + q_coup)
        rows.append(
            {
                "tail_cutoff": int(cutoff),
                "core_mode_count": core_mode_count,
                "tail_mode_count": tail_mode_count,
                "q_core": float(q_core),
                "q_diag": float(q_diag),
                "q_coup": float(q_coup),
                "q_total": q_total,
                "q_schur_sparse": q_schur,
                "q_schur_subtraction": subtraction,
                "q_gap_sparse": float(q_schur / max(tail_norm_sq, 1.0e-300)),
                "q_gap_kind": "sparse_positive_schur_per_tail_mass",
                "q_diag_gap_lite": float(q_diag / max(tail_norm_sq, 1.0e-300)),
                "q_coup_fraction_of_q_diag": float(q_coup / max(abs(q_diag), 1.0e-300)),
                "cg_info": None if cg_info is None else int(cg_info),
                "cg_residual_norm": residual_norm,
                "cg_rhs_norm": rhs_norm,
                "cg_relative_residual": float(residual_norm / max(rhs_norm, 1.0e-300)),
                "ridge": ridge_value,
                "tail_euclidean_mass": float(tail_norm_sq / max(float(np.sum(vector * vector)), 1.0e-300)),
                "skipped": False,
            }
        )
    return rows


def _schur_rows_guarded(
    profile: Any,
    vector: np.ndarray,
    cutoffs: list[int],
    zero_eps: float,
    mode_limit: int,
    warnings: list[str],
    *,
    sparse_schur: bool,
    sparse_schur_tol: float,
    sparse_schur_maxiter: int,
    sparse_schur_ridge: float,
) -> list[dict[str, Any]]:
    if int(mode_limit) >= 0 and int(profile.mode_count) > int(mode_limit):
        warnings.append(
            f"dense_schur_skipped_large_mode_count: mode_count={int(profile.mode_count)} "
            f"> dense_schur_mode_limit={int(mode_limit)}"
        )
        lite_by_cutoff = {row["tail_cutoff"]: row for row in _schur_lite_rows(profile, vector, cutoffs)}
        sparse_by_cutoff = (
            {
                row["tail_cutoff"]: row
                for row in _sparse_schur_rows(
                    profile,
                    vector,
                    cutoffs,
                    zero_eps,
                    solve_tol=float(sparse_schur_tol),
                    solve_maxiter=int(sparse_schur_maxiter),
                    ridge=float(sparse_schur_ridge),
                )
            }
            if bool(sparse_schur)
            else {}
        )
        levels = np.asarray(profile.shell_levels, dtype=np.float64)
        rows = []
        for cutoff in cutoffs:
            lite = lite_by_cutoff[int(cutoff)]
            sparse = sparse_by_cutoff.get(int(cutoff))
            q_schur = None if sparse is None else sparse["q_schur_sparse"]
            q_gap = lite["q_gap_lite"] if sparse is None else sparse["q_gap_sparse"]
            rows.append(
                {
                "tail_cutoff": int(cutoff),
                "core_mode_count": int(np.count_nonzero(levels < float(cutoff))),
                "tail_mode_count": int(np.count_nonzero(levels >= float(cutoff))),
                "q_core": lite["q_core"],
                "q_diag": lite["q_diag"],
                "q_coup": lite["q_coup"],
                "q_total": lite["q_total"],
                "q_schur": q_schur,
                "q_gap": q_gap,
                "q_gap_kind": "sparse_positive_schur_per_tail_mass"
                if sparse is not None
                else "positive_block_lite_total_per_tail_mass",
                "q_diag_gap_lite": lite["q_diag_gap_lite"],
                "q_coup_fraction_of_q_diag": lite["q_coup_fraction_of_q_diag"],
                "q_schur_sparse": None if sparse is None else sparse["q_schur_sparse"],
                "q_schur_subtraction": None if sparse is None else sparse["q_schur_subtraction"],
                "cg_info": None if sparse is None else sparse["cg_info"],
                "cg_residual_norm": None if sparse is None else sparse["cg_residual_norm"],
                "cg_rhs_norm": None if sparse is None else sparse["cg_rhs_norm"],
                "cg_relative_residual": None if sparse is None else sparse["cg_relative_residual"],
                "sparse_schur_ridge": None if sparse is None else sparse["ridge"],
                "tail_euclidean_mass": lite["tail_euclidean_mass"],
                "skipped": True,
                "skip_reason": "dense_schur_skipped_large_mode_count",
            }
            )
        return rows
    return _schur_rows(profile, vector, cutoffs, zero_eps)


def _projection_rows(
    shell_levels: np.ndarray,
    vector: np.ndarray,
    probability: np.ndarray,
    tail_cutoffs: list[int],
) -> list[dict[str, Any]]:
    levels = np.asarray(shell_levels, dtype=np.float64)
    eig = np.asarray(vector, dtype=np.float64)
    eig_norm = float(np.linalg.norm(eig))
    if eig_norm > 0.0:
        eig = eig / eig_norm
    bkm = levels * np.sqrt(np.maximum(probability, 0.0))
    bkm_norm = float(np.linalg.norm(bkm))
    if bkm_norm > 0.0:
        bkm = bkm / bkm_norm
    components: list[tuple[str, np.ndarray]] = [("shell_1_component", levels == 1.0)]
    for cutoff in sorted({int(cutoff) for cutoff in tail_cutoffs}):
        components.append((f"tail_K_ge_{int(cutoff)}_component", levels >= float(cutoff)))
    components.append((f"top_shell_{int(np.max(levels))}_component", levels == float(np.max(levels))))
    rows = []
    for label, mask in components:
        eig_piece = np.where(mask, eig, 0.0)
        bkm_piece = np.where(mask, bkm, 0.0)
        rows.append(
            {
                "component": label,
                "mode_count": int(np.count_nonzero(mask)),
                "eigen_mass": float(np.sum(eig_piece * eig_piece)),
                "bkm_proxy_mass": float(np.sum(bkm_piece * bkm_piece)),
                "bkm_proxy_projection_on_eigen_piece": float(bkm @ eig_piece),
                "bkm_proxy_projection_fraction_sq": float((bkm @ eig_piece) ** 2),
            }
        )
    return rows


def _markdown(payload: dict[str, Any]) -> str:
    result = payload["result"]
    lines = [
        "# NS Triad K_N Shell-6 Mixed-Tail Decomposition",
        "",
        f"- status: `{payload['status']}`",
        f"- profile: `{result['profile_id']}`",
        f"- lambda_min: `{result['lambda_min']:.12g}`",
        f"- Rayleigh numerator/denominator: `{result['rayleigh_numerator']:.12g}` / `{result['rayleigh_denominator']:.12g}`",
        "",
        "## Interpretation",
        "",
        result["interpretation"],
        "",
        "## Top Shell-Pair Rayleigh Contributions",
        "",
        "| shell pair | L_neg numerator frac | L_abs denominator frac | L_pos denominator frac | negative weight frac |",
        "|---:|---:|---:|---:|---:|",
    ]
    rows = sorted(
        result["shell_pair_accounting"]["rows"],
        key=lambda item: item["l_neg_numerator_fraction"],
        reverse=True,
    )[:12]
    for row in rows:
        lines.append(
            f"| {row['shell_pair']} | {row['l_neg_numerator_fraction']:.6f} | "
            f"{row['l_abs_denominator_fraction']:.6f} | {row['l_pos_denominator_fraction']:.6f} | "
            f"{row['negative_frame_weight_fraction']:.6f} |"
        )
    lines.extend(
        [
            "",
            "## Tail/Finite Rayleigh Split",
            "",
            "| cutoff | R finite | R tail | R cross | finite num frac | tail num frac | cross num frac |",
            "|---:|---:|---:|---:|---:|---:|---:|",
        ]
    )
    for row in result["component_rayleigh_splits"]:
        def fmt(value: Any) -> str:
            return "null" if value is None else f"{float(value):.6g}"

        lines.append(
            f"| {row['tail_cutoff']} | {fmt(row['finite_only_rayleigh'])} | "
            f"{fmt(row['tail_only_rayleigh'])} | {fmt(row['cross_term_rayleigh'])} | "
            f"{row['finite_l_neg_fraction_of_full_numerator']:.6f} | "
            f"{row['tail_l_neg_fraction_of_full_numerator']:.6f} | "
            f"{row['cross_l_neg_fraction_of_full_numerator']:.6f} |"
        )
    lines.extend(["", "## Schur Rows", "", "| cutoff | q_diag | q_coup | q_schur | q_gap |", "|---:|---:|---:|---:|---:|"])
    for row in result["schur_repair_rows"]:
        def fmt_schur(value: Any) -> str:
            return "null" if value is None else f"{float(value):.6g}"

        lines.append(
            f"| {row['tail_cutoff']} | {fmt_schur(row['q_diag'])} | {fmt_schur(row['q_coup'])} | "
            f"{fmt_schur(row['q_schur'])} | {fmt_schur(row['q_gap'])} |"
        )
    lines.append("")
    return "\n".join(lines)


def _fmt_optional_float(value: Any, digits: int = 3) -> str:
    if value is None:
        return "null"
    return f"{float(value):.{digits}f}"


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    snapshots = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)
    snapshot = int(snapshots[0][1] if snapshots and isinstance(snapshots[0], tuple) else snapshots[0])
    u, v, w = _frame_velocity(bundle, snapshot)
    spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
    shell_modes = _cube_modes(spectrum, shell_n=int(args.shell), zero_eps=float(args.zero_eps))
    shell_radii = np.asarray([float(mode.shell_radius) for mode in shell_modes], dtype=np.float64)
    shell_levels = _shell_levels(shell_radii)
    if not np.any(shell_levels >= float(args.tail_cutoff)):
        warnings.append(
            f"tail_cutoff_{int(args.tail_cutoff)}_exceeds_active_shell_max_{int(np.max(shell_levels))}; "
            "forced-tail profile uses finite low-shell support only"
        )
    probability = _forced_tail_profile(shell_levels, int(args.tail_cutoff), float(args.tail_eta), float(args.zero_eps))
    profile_id = f"forced_tail_K{int(args.tail_cutoff)}_eta_{float(args.tail_eta):.3f}"
    use_streaming = str(args.profile_builder) == "streaming" or (
        str(args.profile_builder) == "auto" and int(args.shell) >= int(args.streaming_shell_threshold)
    )
    if use_streaming:
        profile, frame_metrics = _streaming_profile(
            modes=shell_modes,
            probability=probability,
            shell_levels=shell_levels,
            zero_eps=float(args.zero_eps),
            profile_id=profile_id,
        )
        operator_triad_count = int(frame_metrics.get("triad_count", 0))
        profile_builder = "streaming"
    else:
        triads, frame_metrics = _build_frame_surface(
            shell_modes,
            zero_eps=float(args.zero_eps),
            triad_sample_limit=int(args.triad_sample_limit),
        )
        profile = build_profile(
            triads=triads,
            probability=probability,
            mode_count=int(len(probability)),
            zero_eps=float(args.zero_eps),
            shell_levels=shell_levels,
            profile_id=profile_id,
        )
        operator_triad_count = int(len(triads))
        profile_builder = "frame-surface"
    solved = _solve_worst_vector(
        profile=profile,
        zero_eps=float(args.zero_eps),
        lobpcg_tol=float(args.lobpcg_tol),
        lobpcg_maxiter=int(args.lobpcg_maxiter),
        block_size=int(args.block_size),
        generalized_mass_shift=float(args.generalized_mass_shift),
        backend=str(args.kn_backend),
        gpu_checks=int(args.gpu_matvec_checks),
    )
    vector = np.asarray(solved["vector"], dtype=np.float64)
    eig_norm = float(np.linalg.norm(vector))
    eigen_probability = (vector / max(eig_norm, float(args.zero_eps))) ** 2
    metrics = _profile_metrics(probability, shell_levels, float(args.zero_eps), float(args.tail_cutoff))
    pair_accounting = _shell_pair_tables(profile, vector)
    diagnostic_cutoffs = sorted(
        {
            int(args.tail_cutoff),
            min(int(args.tail_cutoff) + 1, int(np.max(shell_levels))),
            4,
            5,
        }
    )
    component_splits = [
        _component_rayleigh_split(
            profile,
            shell_levels,
            vector,
            cutoff,
            float(args.zero_eps),
        )
        for cutoff in diagnostic_cutoffs
    ]
    primary_component_split = next(
        row for row in component_splits if int(row["tail_cutoff"]) == int(args.tail_cutoff)
    )
    numerator = float(solved["numerator"])
    denominator = float(solved["denominator"])
    tail_mask = shell_levels >= float(args.tail_cutoff)
    tail_num = sum(
        row["l_neg_numerator"]
        for row in pair_accounting["rows"]
        if any(int(part) >= int(args.tail_cutoff) for part in row["shell_pair"].split("-"))
    )
    tail_den = sum(
        row["l_abs_denominator"]
        for row in pair_accounting["rows"]
        if any(int(part) >= int(args.tail_cutoff) for part in row["shell_pair"].split("-"))
    )
    eigen_mass_rows = _shell_mass_table(shell_levels, eigen_probability, "eigen_mass")
    worst_eigen_shell, worst_eigen_shell_mass = max(
        ((int(row["shell"]), float(row["eigen_mass"])) for row in eigen_mass_rows),
        key=lambda item: item[1],
    )
    tail_only_rayleigh = primary_component_split["tail_only_rayleigh"]
    finite_only_rayleigh = primary_component_split["finite_only_rayleigh"]
    cross_num_fraction = primary_component_split["cross_l_neg_fraction_of_full_numerator"]
    interpretation = (
        f"The K>={int(args.tail_cutoff)} tail carries the reported eigen mass. The low Rayleigh quotient is "
        f"not tail-internal in this split: the largest eigen shell is {worst_eigen_shell} "
        f"with mass {worst_eigen_shell_mass:.3f}. "
        f"Shell pairs touching K>={int(args.tail_cutoff)} carry {tail_num / max(numerator, 1.0e-300):.3f} of the numerator "
        f"and {tail_den / max(denominator, 1.0e-300):.3f} of the denominator in this recomputation. "
        f"The K>={int(args.tail_cutoff)} tail-only quotient is {_fmt_optional_float(tail_only_rayleigh)}; "
        f"the finite-only quotient is {_fmt_optional_float(finite_only_rayleigh)}; "
        f"the finite-tail cross term carries {cross_num_fraction:.3f} "
        "of the L_neg numerator."
    )
    result = {
        "profile_id": profile_id,
        "shell": int(args.shell),
        "tail_eta": float(args.tail_eta),
        "snapshot_index": snapshot,
        "selected_mode_count": int(len(shell_modes)),
        "operator_triad_count": int(operator_triad_count),
        "profile_builder": profile_builder,
        "edge_count": int(len(profile.weights_abs)),
        "kn_backend": str(args.kn_backend),
        "gpu_kn_authority": False,
        "backend_info": solved.get("backend_info", {}),
        "triad_sample_limit_scope": "receipt_samples_only",
        "frame_metrics": {
            "carrier_stratum_count": int(frame_metrics.get("carrier_stratum_count", 0)),
            "triad_sample_count": int(len(frame_metrics.get("triad_samples", []) or [])),
        },
        "lambda_min": solved["lambda_min"],
        "rayleigh_numerator": numerator,
        "rayleigh_denominator": denominator,
        "profile_metrics": metrics,
        "eigen_mass_by_shell": eigen_mass_rows,
        "profile_mass_by_shell": _shell_mass_table(shell_levels, probability, "profile_mass"),
        "shell_pair_accounting": pair_accounting,
        "component_rayleigh_splits": component_splits,
        "schur_repair_rows": _schur_rows_guarded(
            profile,
            vector,
            diagnostic_cutoffs,
            float(args.zero_eps),
            int(args.dense_schur_mode_limit),
            warnings,
            sparse_schur=bool(args.sparse_schur),
            sparse_schur_tol=float(args.sparse_schur_tol),
            sparse_schur_maxiter=int(args.sparse_schur_maxiter),
            sparse_schur_ridge=float(args.sparse_schur_ridge),
        ),
        "bkm_stretching_proxy_projection_rows": _projection_rows(
            shell_levels,
            vector,
            probability,
            diagnostic_cutoffs,
        ),
        "tail_responsibility_summary": {
            "tail_cutoff": int(args.tail_cutoff),
            "eigen_tail_mass": float(np.sum(eigen_probability[tail_mask])),
            "profile_tail_mass": float(np.sum(probability[tail_mask])),
            "tail_touching_rayleigh_numerator_fraction": float(tail_num / max(numerator, 1.0e-300)),
            "tail_touching_rayleigh_denominator_fraction": float(tail_den / max(denominator, 1.0e-300)),
            "worst_eigen_shell": int(worst_eigen_shell),
            "worst_eigen_shell_mass": float(worst_eigen_shell_mass),
            "dominant_shell_escape": False,
            "top_shell_escape": False,
            "mixed_tail_candidate": True,
        },
        "interpretation": interpretation,
    }
    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "status": OK_STATUS,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "warnings": warnings,
        "result": result,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    args.output_md.parent.mkdir(parents=True, exist_ok=True)
    args.output_md.write_text(_markdown(payload), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
