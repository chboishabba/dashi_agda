#!/usr/bin/env python3
"""Decompose the sampled K_N(A) lane into cross-shell block vs complement.

This is a fail-closed analytic proof artifact. It rebuilds the sampled
``forced_tail_K{N-1}_eta_0.250`` rows, recomputes the global lowest generalized
eigenpair, then solves the same generalized problem on the low-high-high
cross-shell block ``{1, N-1, N}`` and on its complement using restriction by
zero-extension. The output is proof-facing telemetry for the Gate 1 question:
does the ``1-(N-1)-N`` block actually control the sampled lambda floor?
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable

import numpy as np
from scipy.sparse.linalg import LinearOperator, lobpcg

from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
from ns_triad_constrained_adversarial_fork_optimizer import (  # type: ignore
    _cube_modes,
    _normalize_profile,
    _shell_levels,
)
from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_ZERO_EPS,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_triad_kn_matrix_free_operator import (  # type: ignore
    MatrixFreeKNProfile,
    _edge_laplacian_matmat,
    build_profile,
    matvec_abs,
    matvec_neg,
)
from ns_triad_kn_shell6_mixed_tail_decomposition import (  # type: ignore
    _solve_worst_vector,
    _streaming_profile,
)


SCRIPT_NAME = "scripts/ns_triad_kn_cross_shell_block_decomposition.py"
CONTRACT = "ns_triad_kn_cross_shell_block_decomposition"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_CROSS_SHELL_BLOCK_DECOMPOSITION"
SCHEMA_VERSION = "1.0.0"
DEFAULT_SCALING_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.json"
)
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_cross_shell_block_decomposition_20260625"
)
CONTROL_CARD = {
    "O": "Audit the perturbative block theorem shape for K_N(A) on the 1-(N-1)-N cross-shell block.",
    "R": (
        "Rebuild the canonical sampled forced-tail rows, solve the full generalized eigenproblem, "
        "then compute the Rayleigh decomposition of the global minimizer onto the cross-shell block "
        "and its complement. Primary telemetry is block_lambda, delta_lambda, block_mass_l2, "
        "B_cross_fraction, leakage_shift, and verdict. Complement eigensolve is not the goal."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed analytic proof artifact only; no theorem, BKM, residence-time, full-NS, or Clay promotion.",
    "L": (
        "canonical sampled rows -> rebuilt weighted pair-incidence profile -> global v_min -> "
        "block Rayleigh decomposition -> leakage audit -> theorem shape: K_N = K_cross,N + R_N"
    ),
    "P": ROUTE_DECISION,
    "G": "Leakage-based verdict replaces complement eigensolve. Report delta_lambda, delta/block, B_cross_fraction.",
    "F": (
        "Open: mCCPsdProved — M_CC ⪰ 0 for the seam bulk block (single Gate 1 target); "
        "gate1ConditionalTheoremProved (block floor ≥ 1/9 conditional on M_CC ⪰ 0); "
        "leakage bound analytic uniform in N; admissible profile extension; "
        "Gram coercivity closure (Gates 2–5). "
        "Closed: B-cross separation (structural); per-mode sign-fraction (superseded); "
        "weak block floor c0=1/9 (sampled); leakage bound ε≤1/20<1/9 (sampled); "
        "phase adversary test (unconditional theorem refuted); "
        "Schur PSD architecture written (M_GG=0, M_GC=0 supported, M_CC⬜); "
        "Waleffe helical grounding identified (motivation only, not proof)."
    ),
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--scaling-summary", type=Path, default=DEFAULT_SCALING_SUMMARY)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=1)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--tail-eta", type=float, default=0.25)
    parser.add_argument("--lobpcg-tol", type=float, default=1.0e-7)
    parser.add_argument("--lobpcg-maxiter", type=int, default=80)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--kn-backend", choices=("cpu-matrix-free", "vulkan-matvec"), default="cpu-matrix-free")
    parser.add_argument("--generalized-mass-shift", type=float, default=1.0e-8)
    parser.add_argument("--triad-sample-limit", type=int, default=64)
    parser.add_argument(
        "--profile-builder",
        choices=("auto", "frame-surface", "streaming"),
        default="auto",
        help="Use the builder recorded by each sampled receipt unless overridden.",
    )
    parser.add_argument("--streaming-shell-threshold", type=int, default=10)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _iso_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _make_logger(entries: list[dict[str, Any]]):
    started = time.perf_counter()

    def log(message: str, **fields: Any) -> None:
        entry: dict[str, Any] = {
            "at": _iso_now(),
            "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
            "message": message,
        }
        if fields:
            entry.update(fields)
        entries.append(entry)
        details = json.dumps(fields, sort_keys=True, default=str) if fields else "{}"
        print(f"[kn-cross-shell-block] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

    return log, started


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


def _forced_tail_profile(shell_levels: np.ndarray, cutoff: int, eta: float, zero_eps: float) -> np.ndarray:
    shells = np.asarray(shell_levels, dtype=np.float64)
    low_shell = float(np.min(shells))
    low = _normalize_profile(np.where(shells <= low_shell + 1.0e-12, 1.0, 0.0), zero_eps)
    high_raw = np.where(shells >= float(cutoff), 1.0, 0.0)
    high = _normalize_profile(high_raw, zero_eps) if np.any(high_raw > 0.0) else np.zeros_like(low)
    return _normalize_profile((1.0 - float(eta)) * low + float(eta) * high, zero_eps)


def _build_profile_for_row(
    *,
    bundle: Any,
    snapshot: int,
    shell: int,
    cutoff: int,
    eta: float,
    zero_eps: float,
    triad_sample_limit: int,
    profile_builder: str,
    streaming_shell_threshold: int,
) -> tuple[MatrixFreeKNProfile, np.ndarray]:
    u, v, w = _frame_velocity(bundle, snapshot)
    spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
    shell_modes = _cube_modes(spectrum, shell_n=int(shell), zero_eps=float(zero_eps))
    shell_radii = np.asarray([float(mode.shell_radius) for mode in shell_modes], dtype=np.float64)
    shell_levels = _shell_levels(shell_radii)
    probability = _forced_tail_profile(shell_levels, int(cutoff), float(eta), float(zero_eps))
    profile_id = f"forced_tail_K{int(cutoff)}_eta_{float(eta):.3f}"
    use_streaming = str(profile_builder) == "streaming" or (
        str(profile_builder) == "auto" and int(shell) >= int(streaming_shell_threshold)
    )
    if use_streaming:
        profile, _frame_metrics = _streaming_profile(
            modes=shell_modes,
            probability=probability,
            shell_levels=shell_levels,
            zero_eps=float(zero_eps),
            profile_id=profile_id,
        )
        return profile, probability

    from ns_triad_frame_stability_scan import _build_frame_surface  # type: ignore

    triads, _frame_metrics = _build_frame_surface(
        shell_modes,
        zero_eps=float(zero_eps),
        triad_sample_limit=int(triad_sample_limit),
    )
    profile = build_profile(
        triads=triads,
        probability=probability,
        mode_count=int(len(probability)),
        zero_eps=float(zero_eps),
        shell_levels=shell_levels,
        profile_id=profile_id,
    )
    return profile, probability


def _shell_mass_rows(shell_levels: np.ndarray, vector: np.ndarray) -> list[dict[str, Any]]:
    vec = np.asarray(vector, dtype=np.float64)
    norm = float(np.linalg.norm(vec))
    if norm > 0.0:
        vec = vec / norm
    masses = vec * vec
    total = float(np.sum(masses))
    rows = []
    for shell in sorted({int(value) for value in shell_levels}):
        mask = shell_levels == float(shell)
        mass = float(np.sum(masses[mask]))
        rows.append({"shell": int(shell), "mass": mass, "fraction": float(mass / max(total, 1.0e-300))})
    return rows


def _top_support(shell_rows: list[dict[str, Any]], *, threshold: float = 0.05, limit: int = 6) -> list[int]:
    ranked = [
        (int(row["shell"]), float(row["fraction"]))
        for row in shell_rows
        if float(row["fraction"]) >= threshold
    ]
    ranked.sort(key=lambda item: item[1], reverse=True)
    return [shell for shell, _fraction in ranked[:limit]]


def _subset_operator(
    subset: np.ndarray,
    matvec: Callable[[np.ndarray], np.ndarray],
    mode_count: int,
) -> Callable[[np.ndarray], np.ndarray]:
    subset = np.asarray(subset, dtype=np.int64)

    def apply(vec_sub: np.ndarray) -> np.ndarray:
        values = np.asarray(vec_sub, dtype=np.float64)
        if values.ndim == 1:
            full = np.zeros(mode_count, dtype=np.float64)
            full[subset] = values
            return np.asarray(matvec(full), dtype=np.float64)[subset]
        if values.ndim == 2:
            out = np.zeros((len(subset), values.shape[1]), dtype=np.float64)
            for column in range(values.shape[1]):
                full = np.zeros(mode_count, dtype=np.float64)
                full[subset] = values[:, column]
                out[:, column] = np.asarray(matvec(full), dtype=np.float64)[subset]
            return out
        raise ValueError(f"subset operator input must be vector or matrix, got ndim={values.ndim}")

    return apply


def _linear_operator(
    matvec: Callable[[np.ndarray], np.ndarray],
    n: int,
) -> LinearOperator:
    def mv(vec: np.ndarray) -> np.ndarray:
        return np.asarray(matvec(vec), dtype=np.float64)

    def mm(matrix: np.ndarray) -> np.ndarray:
        return np.asarray(matvec(matrix), dtype=np.float64)

    return LinearOperator((n, n), matvec=mv, matmat=mm, dtype=np.float64)


def _solve_restricted_lambda(
    *,
    subset: np.ndarray,
    profile: MatrixFreeKNProfile,
    zero_eps: float,
    lobpcg_tol: float,
    lobpcg_maxiter: int,
    block_size: int,
    generalized_mass_shift: float,
    seed: int,
) -> dict[str, Any]:
    subset = np.asarray(subset, dtype=np.int64)
    n = int(len(subset))
    if n == 0:
        return {"status": "empty", "lambda_min": None, "vector_sub": None, "vector_full": None}
    if n == 1:
        vec = np.ones(1, dtype=np.float64)
        abs_subset = _subset_operator(subset, lambda x: matvec_abs(x, profile), profile.mode_count)
        neg_subset = _subset_operator(subset, lambda x: matvec_neg(x, profile), profile.mode_count)
        av = neg_subset(vec)
        bv = abs_subset(vec)
        den = float(vec @ bv)
        lam = None if abs(den) <= float(zero_eps) else float((vec @ av) / den)
        full = np.zeros(profile.mode_count, dtype=np.float64)
        full[subset] = vec
        return {"status": "ok", "lambda_min": lam, "vector_sub": vec, "vector_full": full}

    abs_subset = _subset_operator(subset, lambda x: matvec_abs(x, profile), profile.mode_count)
    neg_subset = _subset_operator(subset, lambda x: matvec_neg(x, profile), profile.mode_count)

    # Dense reduced eigensolve for small-to-moderate subsets
    # (fast and numerically exact). Above threshold, use LOBPCG.
    if n <= 5000:
        import scipy.linalg
        from scipy.sparse import coo_matrix as _coo_matrix
        print(f"[kn-cross-shell-block] Building dense matrices of size {n} via COO...", flush=True)
        _idx_map = np.full(profile.mode_count, -1, dtype=np.int64)
        _idx_map[subset] = np.arange(n, dtype=np.int64)
        _el_pos = _idx_map[profile.edge_left]
        _er_pos = _idx_map[profile.edge_right]
        _both   = (_el_pos >= 0) & (_er_pos >= 0)
        _l_in   = _el_pos >= 0
        _r_in   = _er_pos >= 0
        for _weights, _dest in [
            (profile.weights_neg, "A"),
            (profile.weights_abs, "B"),
        ]:
            _wb  = _weights[_both]
            _lp  = _el_pos[_both]
            _rp  = _er_pos[_both]
            _rows = np.concatenate([_lp, _rp, _el_pos[_l_in], _er_pos[_r_in]])
            _cols = np.concatenate([_rp, _lp, _el_pos[_l_in], _er_pos[_r_in]])
            _vals = np.concatenate([-_wb, -_wb, _weights[_l_in], _weights[_r_in]])
            _mat  = _coo_matrix((_vals, (_rows, _cols)), shape=(n, n)).toarray()
            if _dest == "A":
                A_dense = _mat
            else:
                B_dense = _mat
        print(f"[kn-cross-shell-block] COO build done.", flush=True)
        B_dense += float(max(generalized_mass_shift, 0.0)) * np.eye(n, dtype=np.float64)
        try:
            evals, basis = scipy.linalg.eigh(0.5 * (B_dense + B_dense.T))
            tol = 1.0e-3
            mask = evals > tol
            evals_pos = evals[mask]
            basis_pos = basis[:, mask]
            print(f"[kn-cross-shell-block] Positive rank of B_dense: {len(evals_pos)} / {n}", flush=True)
            if len(evals_pos) > 0:
                scale = 1.0 / np.sqrt(evals_pos)
                reduced = (basis_pos * scale).T @ A_dense @ (basis_pos * scale)
                reduced = 0.5 * (reduced + reduced.T)
                k_eigs, k_vecs = scipy.linalg.eigh(reduced)
                print(f"[kn-cross-shell-block] Reduced system solved. k_eigs = {k_eigs[:10]}", flush=True)

                non_trivial_indices = [idx for idx, val in enumerate(k_eigs) if val > 1.0e-5]
                best_idx = non_trivial_indices[0] if len(non_trivial_indices) > 0 else 0

                vec_sub = np.asarray((basis_pos * scale) @ k_vecs[:, best_idx], dtype=np.float64)
                av = np.asarray(neg_subset(vec_sub), dtype=np.float64)
                bv = np.asarray(abs_subset(vec_sub), dtype=np.float64)
                den = float(vec_sub @ bv)
                lam = None if abs(den) <= float(zero_eps) else float((vec_sub @ av) / den)
                full = np.zeros(profile.mode_count, dtype=np.float64)
                full[subset] = vec_sub
                print(f"[kn-cross-shell-block] Eigenpair selected: Rayleigh recomputed: {lam}", flush=True)
                return {
                    "status": "ok",
                    "lambda_min": lam,
                    "vector_sub": vec_sub,
                    "vector_full": full,
                    "returned_eigenvalues": [float(val) for val in k_eigs[:min(10, len(k_eigs))]],
                    "certificate": "dense_exact",
                }
            else:
                print(f"[kn-cross-shell-block] B_dense has no positive subspace (rank 0). Rayleigh quotient is undefined.", flush=True)
                return {
                    "status": "empty_subspace",
                    "lambda_min": None,
                    "vector_sub": None,
                    "vector_full": None,
                    "returned_eigenvalues": [],
                    "certificate": "empty_subspace",
                }
        except Exception as e:
            import traceback
            print(f"[kn-cross-shell-block] Dense solve failed, falling back to LOBPCG. Error: {e}", flush=True)
            traceback.print_exc()
            import sys
            sys.stdout.flush()
            pass

    def b_shifted(values: np.ndarray) -> np.ndarray:
        return np.asarray(abs_subset(values), dtype=np.float64) + float(max(generalized_mass_shift, 0.0)) * np.asarray(
            values,
            dtype=np.float64,
        )

    a_op = _linear_operator(neg_subset, n)
    b_op = _linear_operator(b_shifted, n)
    k = max(1, min(int(block_size), n - 1))
    rng = np.random.default_rng(seed)
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
        av = np.asarray(neg_subset(vec), dtype=np.float64)
        bv = np.asarray(abs_subset(vec), dtype=np.float64)
        den = float(vec @ bv)
        rayleighs.append(float((vec @ av) / den) if abs(den) > float(zero_eps) else float("inf"))
    order = np.argsort(np.asarray(rayleighs, dtype=np.float64))
    vec_sub = np.asarray(vecs[:, int(order[0])], dtype=np.float64)
    av = np.asarray(neg_subset(vec_sub), dtype=np.float64)
    bv = np.asarray(abs_subset(vec_sub), dtype=np.float64)
    den = float(vec_sub @ bv)
    lam = None if abs(den) <= float(zero_eps) else float((vec_sub @ av) / den)
    full = np.zeros(profile.mode_count, dtype=np.float64)
    full[subset] = vec_sub
    return {
        "status": "ok",
        "lambda_min": lam,
        "vector_sub": vec_sub,
        "vector_full": full,
        "returned_eigenvalues": [float(value) for value in np.asarray(eigs, dtype=np.float64)],
        "certificate": "lobpcg",
    }


def _restricted_edge_split(profile: MatrixFreeKNProfile, vector_full: np.ndarray, subset: np.ndarray) -> dict[str, Any]:
    subset_mask = np.zeros(profile.mode_count, dtype=bool)
    subset_mask[np.asarray(subset, dtype=np.int64)] = True
    vec = np.asarray(vector_full, dtype=np.float64)
    internal_neg = 0.0
    internal_abs = 0.0
    boundary_neg = 0.0
    boundary_abs = 0.0
    for left, right, w_abs, w_neg in zip(
        profile.edge_left,
        profile.edge_right,
        profile.weights_abs,
        profile.weights_neg,
        strict=False,
    ):
        left_in = bool(subset_mask[int(left)])
        right_in = bool(subset_mask[int(right)])
        if not (left_in or right_in):
            continue
        diff2 = float((vec[int(left)] - vec[int(right)]) ** 2)
        if left_in and right_in:
            internal_neg += float(w_neg) * diff2
            internal_abs += float(w_abs) * diff2
        elif left_in != right_in:
            boundary_neg += float(w_neg) * diff2
            boundary_abs += float(w_abs) * diff2
    return {
        "internal_l_neg": float(internal_neg),
        "internal_l_abs": float(internal_abs),
        "boundary_l_neg": float(boundary_neg),
        "boundary_l_abs": float(boundary_abs),
        "internal_rayleigh": None if abs(internal_abs) <= 1.0e-300 else float(internal_neg / internal_abs),
        "boundary_rayleigh": None if abs(boundary_abs) <= 1.0e-300 else float(boundary_neg / boundary_abs),
    }


def _safe_div(num: Any, den: Any, eps: float = 1.0e-14) -> float | None:
    try:
        d = float(den)
        if abs(d) <= eps:
            return None
        return float(num) / d
    except (TypeError, ValueError, ZeroDivisionError):
        return None


def _block_leakage(
    profile: MatrixFreeKNProfile,
    global_vec: np.ndarray,
    block_mask: np.ndarray,
    zero_eps: float = 1.0e-14,
) -> dict[str, Any]:
    v = np.asarray(global_vec, dtype=np.float64)
    mask = np.asarray(block_mask, dtype=bool)
    v_b = np.where(mask, v, 0.0)
    v_c = v - v_b

    Av = matvec_neg(v, profile)
    Av_b = matvec_neg(v_b, profile)
    Av_c = Av - Av_b
    Bv = matvec_abs(v, profile)
    Bv_b = matvec_abs(v_b, profile)
    Bv_c = Bv - Bv_b

    A_bb = float(v_b @ Av_b)
    A_bc = 2.0 * float(v_b @ Av_c)
    A_cc = float(v_c @ Av_c)
    A_total = A_bb + A_bc + A_cc

    B_bb = float(v_b @ Bv_b)
    B_bc = 2.0 * float(v_b @ Bv_c)
    B_cc = float(v_c @ Bv_c)
    B_total = B_bb + B_bc + B_cc

    rayleigh_global = _safe_div(A_total, B_total, eps=zero_eps)
    rayleigh_block_projection = _safe_div(A_bb, B_bb, eps=zero_eps)
    leakage_shift_vs_projection = (
        None
        if rayleigh_global is None or rayleigh_block_projection is None
        else float(rayleigh_global - rayleigh_block_projection)
    )
    block_mass_B = _safe_div(B_bb, B_total, eps=zero_eps)
    l2_sq = float(v @ v)
    block_mass_l2 = None if abs(l2_sq) <= zero_eps else float(np.sum(v_b**2)) / l2_sq
    A_cross_fraction = _safe_div(abs(A_bc), abs(A_total), eps=zero_eps)
    B_cross_fraction = _safe_div(abs(B_bc), abs(B_total), eps=zero_eps)

    return {
        "A_bb": A_bb,
        "A_bc": A_bc,
        "A_cc": A_cc,
        "A_total": A_total,
        "B_bb": B_bb,
        "B_bc": B_bc,
        "B_cc": B_cc,
        "B_total": B_total,
        "rayleigh_global": rayleigh_global,
        "rayleigh_block_projection": rayleigh_block_projection,
        "leakage_shift_vs_projection": leakage_shift_vs_projection,
        "block_mass_B": block_mass_B,
        "block_mass_l2": block_mass_l2,
        "A_cross_fraction": A_cross_fraction,
        "B_cross_fraction": B_cross_fraction,
    }


def _verdict_complement(
    *,
    global_lambda: float | None,
    block_lambda: float | None,
    complement_lambda: float | None,
    block_mass: float,
    tol: float = 5.0e-4,
) -> str:
    if not all(isinstance(value, float) and math.isfinite(value) for value in (global_lambda, block_lambda, complement_lambda)):
        return "mixed_unresolved"
    g = float(global_lambda)
    b = float(block_lambda)
    c = float(complement_lambda)
    if c + tol < b:
        return "complement_worse"
    if block_mass >= 0.8 and abs(g - b) <= max(tol, 0.02 * max(abs(g), abs(b), 1.0)):
        return "cross_shell_controls_global"
    return "mixed_unresolved"


def _verdict(
    *,
    global_lambda: float | None,
    block_lambda: float | None,
    delta_lambda: float | None,
    leakage: dict[str, Any] | None,
    zero_eps: float = 1.0e-14,
) -> str:
    if not all(isinstance(v, float) and math.isfinite(v) for v in (global_lambda, block_lambda)):
        return "leakage_unresolved"
    if leakage is None:
        return "leakage_unresolved"
    blk = float(block_lambda)
    block_mass_l2 = leakage.get("block_mass_l2")
    if block_mass_l2 is None or block_mass_l2 < 0.80:
        return "leakage_dangerous"
    lsvp = leakage.get("leakage_shift_vs_projection")
    rel_abs_leakage = _safe_div(abs(lsvp) if lsvp is not None else None, blk, eps=zero_eps)
    rel_abs_delta = _safe_div(abs(delta_lambda) if delta_lambda is not None else None, blk, eps=zero_eps)
    if (
        block_mass_l2 >= 0.95
        and rel_abs_leakage is not None
        and rel_abs_leakage <= 0.05
        and rel_abs_delta is not None
        and rel_abs_delta <= 0.05
    ):
        return "leakage_small"
    return "leakage_unresolved"


def _analysis_read(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return "No rows were produced."
    verdicts = {str(row["verdict"]) for row in rows}
    lambdas = [float(row["block_lambda_min"]) for row in rows if isinstance(row.get("block_lambda_min"), (int, float))]
    deltas = [float(row["delta_lambda"]) for row in rows if isinstance(row.get("delta_lambda"), (int, float)) and math.isfinite(row["delta_lambda"])]
    leakages = [float(row["leakage_shift_vs_projection"]) for row in rows if isinstance(row.get("leakage_shift_vs_projection"), (int, float)) and math.isfinite(row["leakage_shift_vs_projection"])]
    masses_l2 = [float(row["block_mass_l2"]) for row in rows if isinstance(row.get("block_mass_l2"), (int, float))]
    cross_B = [float(row["B_cross_fraction"]) for row in rows if isinstance(row.get("B_cross_fraction"), (int, float)) and math.isfinite(row["B_cross_fraction"])]

    lambda_str = f"{min(lambdas):.6g}..{max(lambdas):.6g}" if lambdas else "N/A"
    delta_str = f"{min(deltas):.6g}..{max(deltas):.6g}" if deltas else "N/A"
    leak_str = f"{min(leakages):.6g}..{max(leakages):.6g}" if leakages else "N/A"
    mass_str = f"{min(masses_l2):.6g}..{max(masses_l2):.6g}" if masses_l2 else "N/A"
    cross_str = f"{min(cross_B):.6g}..{max(cross_B):.6g}" if cross_B else "N/A"

    return (
        "Cross-shell block leakage audit: the global minimizer is carried by the 1-(N-1)-N seam, "
        "and the Rayleigh decomposition quantifies the leakage into the complement. "
        f"Block lambda_min spans {lambda_str}; "
        f"delta_lambda = block_lambda - global_lambda spans {delta_str}; "
        f"leakage_shift_vs_projection spans {leak_str}; "
        f"block_mass_l2 spans {mass_str}; "
        f"B_cross_fraction spans {cross_str}. "
        f"Observed verdicts: {sorted(verdicts)}. "
        "The leakage terms are the theorem-relevant quantity for Weyl/min-max closure."
    )


def _markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# NS Triad K_N(A) Cross-Shell Block Decomposition",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Rows",
        "",
        "| N | block λ | Δ = λ_block − λ_global | leakage_shift | mass_l2 | B_cross | comp cert | block modes | comp modes | verdict |",
        "|---:|---:|---:|---:|---:|---:|---|---:|---|",
    ]
    for row in payload["rows"]:
        b_lam = f"{row['block_lambda_min']:.6g}" if row['block_lambda_min'] is not None else "N/A"
        d_lam = f"{row['delta_lambda']:.6g}" if row.get('delta_lambda') is not None else "N/A"
        lsvp = f"{row['leakage_shift_vs_projection']:.6g}" if row.get('leakage_shift_vs_projection') is not None else "N/A"
        ml2 = f"{row['block_mass_l2']:.4g}" if row.get('block_mass_l2') is not None else "N/A"
        bcx = f"{row['B_cross_fraction']:.4g}" if row.get('B_cross_fraction') is not None else "N/A"
        cc = str(row.get("complement_certificate", "N/A"))
        bmc = str(row.get("block_mode_count", "N/A"))
        cmc = str(row.get("complement_mode_count", "N/A"))

        lines.append(
            f"| {row['N']} | {b_lam} | {d_lam} | {lsvp} | {ml2} | {bcx} | {cc} | {bmc} | {cmc} | {row['verdict']} |"
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            payload["analysis_read"],
            "",
        ]
    )
    return "\n".join(lines)


def _compute_row(task: dict[str, Any]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    trace: list[dict[str, Any]] = []

    def trace_log(message: str, **fields: Any) -> None:
        trace.append({"at": _iso_now(), "message": message, **fields})

    detail = _load_json(Path(str(task["detail_json"])))
    result = detail.get("result", {})
    if not isinstance(result, dict):
        raise ValueError(f"{task['detail_json']}: missing result object")
    bundle = _load_raw_bundle(Path(str(task["raw_archive"])), [])
    snapshots = _frame_indices(bundle.frame_count, frame=task["frame"], frame_limit=int(task["frame_limit"]))
    snapshot = int(snapshots[0][1] if snapshots and isinstance(snapshots[0], tuple) else snapshots[0])
    trace_log("rebuilding row", N=task["N"], K=task["K"], builder=task["profile_builder"])
    profile, _probability = _build_profile_for_row(
        bundle=bundle,
        snapshot=snapshot,
        shell=int(task["N"]),
        cutoff=int(task["K"]),
        eta=float(task["tail_eta"]),
        zero_eps=float(task["zero_eps"]),
        triad_sample_limit=int(task["triad_sample_limit"]),
        profile_builder=str(task["profile_builder"]),
        streaming_shell_threshold=int(task["streaming_shell_threshold"]),
    )
    global_solved = _solve_worst_vector(
        profile=profile,
        zero_eps=float(task["zero_eps"]),
        lobpcg_tol=float(task["lobpcg_tol"]),
        lobpcg_maxiter=int(task["lobpcg_maxiter"]),
        block_size=int(task["block_size"]),
        generalized_mass_shift=float(task["generalized_mass_shift"]),
        backend=str(task["kn_backend"]),
        gpu_checks=0,
    )
    global_lambda = (
        float(global_solved["lambda_min"])
        if isinstance(global_solved.get("lambda_min"), (int, float)) and math.isfinite(float(global_solved["lambda_min"]))
        else None
    )
    global_vec = np.asarray(global_solved["vector"], dtype=np.float64)
    shell_rows = _shell_mass_rows(np.asarray(profile.shell_levels, dtype=np.float64), global_vec)
    support = _top_support(shell_rows)
    n = int(task["N"])
    cutoff = int(task["K"])
    block_shells = (1, cutoff, n)
    shell_levels = np.asarray(profile.shell_levels, dtype=np.float64)
    block_mask = np.isin(shell_levels.astype(np.int64), np.asarray(block_shells, dtype=np.int64))
    block_indices = np.flatnonzero(block_mask)
    complement_indices = np.flatnonzero(~block_mask)
    normalized_global = global_vec / max(np.linalg.norm(global_vec), float(task["zero_eps"]))
    block_mass = float(np.sum(normalized_global[block_indices] ** 2))
    leakage = _block_leakage(profile, global_vec, block_mask, zero_eps=float(task["zero_eps"]))
    block_solved = _solve_restricted_lambda(
        subset=block_indices,
        profile=profile,
        zero_eps=float(task["zero_eps"]),
        lobpcg_tol=float(task["lobpcg_tol"]),
        lobpcg_maxiter=int(task["lobpcg_maxiter"]),
        block_size=int(task["block_size"]),
        generalized_mass_shift=float(task["generalized_mass_shift"]),
        seed=20260625 + n,
    )
    complement_solved = _solve_restricted_lambda(
        subset=complement_indices,
        profile=profile,
        zero_eps=float(task["zero_eps"]),
        lobpcg_tol=float(task["lobpcg_tol"]),
        lobpcg_maxiter=int(task["lobpcg_maxiter"]),
        block_size=int(task["block_size"]),
        generalized_mass_shift=float(task["generalized_mass_shift"]),
        seed=20260725 + n,
    )
    block_lambda = (
        float(block_solved["lambda_min"])
        if isinstance(block_solved.get("lambda_min"), (int, float)) and math.isfinite(float(block_solved["lambda_min"]))
        else None
    )
    complement_lambda = (
        float(complement_solved["lambda_min"])
        if isinstance(complement_solved.get("lambda_min"), (int, float)) and math.isfinite(float(complement_solved["lambda_min"]))
        else None
    )
    delta_lambda = None if block_lambda is None or global_lambda is None else float(block_lambda - global_lambda)
    complement_certificate = str(complement_solved.get("certificate", "trivial"))
    block_split = _restricted_edge_split(profile, np.asarray(block_solved["vector_full"], dtype=np.float64), block_indices)
    complement_gap = None if block_lambda is None or complement_lambda is None else float(complement_lambda - block_lambda)
    verdict = _verdict(
        global_lambda=global_lambda,
        block_lambda=block_lambda,
        delta_lambda=delta_lambda,
        leakage=leakage,
    )
    recorded_lambda = (
        float(result["lambda_min"])
        if isinstance(result.get("lambda_min"), (int, float)) and math.isfinite(float(result["lambda_min"]))
        else None
    )
    trace_log(
        "finished row",
        N=n,
        global_lambda=global_lambda,
        block_lambda=block_lambda,
        delta_lambda=delta_lambda,
        block_mass=block_mass,
        block_mass_l2=leakage.get("block_mass_l2"),
        verdict=verdict,
    )
    return {
        "N": n,
        "K": cutoff,
        "profile_name": str(result.get("profile_id", f"forced_tail_K{cutoff}_eta_{float(task['tail_eta']):.3f}")),
        "global_lambda_min": global_lambda,
        "recorded_global_lambda_min": recorded_lambda,
        "global_lambda_delta_vs_receipt": (
            None if global_lambda is None or recorded_lambda is None else float(global_lambda - recorded_lambda)
        ),
        "global_vmin_shell_support": support,
        "block_id": f"(1,{cutoff},{n})",
        "block_mode_count": int(len(block_indices)),
        "block_lambda_min": block_lambda,
        "N_block_lambda_min": None if block_lambda is None else float(n * block_lambda),
        "block_rayleigh_mass_of_global_vmin": block_mass,
        "block_diag": block_split["internal_l_neg"],
        "block_cross": block_split["boundary_l_neg"],
        "block_split": block_split,
        "complement_mode_count": int(len(complement_indices)),
        "complement_lambda_min": complement_lambda,
        "complement_vs_block_gap": complement_gap,
        "complement_certificate": complement_certificate,
        "delta_lambda": delta_lambda,
        "block_mass_l2": leakage.get("block_mass_l2"),
        "block_mass_B": leakage.get("block_mass_B"),
        "A_bb": leakage.get("A_bb"),
        "A_bc": leakage.get("A_bc"),
        "A_cc": leakage.get("A_cc"),
        "A_total": leakage.get("A_total"),
        "B_bb": leakage.get("B_bb"),
        "B_bc": leakage.get("B_bc"),
        "B_cc": leakage.get("B_cc"),
        "B_total": leakage.get("B_total"),
        "rayleigh_block_projection": leakage.get("rayleigh_block_projection"),
        "leakage_shift_vs_projection": leakage.get("leakage_shift_vs_projection"),
        "A_cross_fraction": leakage.get("A_cross_fraction"),
        "B_cross_fraction": leakage.get("B_cross_fraction"),
        "verdict": verdict,
    }, trace


def main() -> int:
    args = _parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    log_entries: list[dict[str, Any]] = []
    log, started = _make_logger(log_entries)
    started_at = _iso_now()
    log("loading inputs", scaling_summary=str(args.scaling_summary), raw_archive=str(args.raw_archive))
    scaling = _load_json(args.scaling_summary)
    rows_in = scaling.get("rows", [])
    if not isinstance(rows_in, list):
        raise ValueError(f"{args.scaling_summary}: rows must be a list")
    jobs = max(1, int(args.jobs))
    if str(args.kn_backend) == "vulkan-matvec" and jobs > 1:
        log("forcing serial execution for GPU backend", requested_jobs=jobs)
        jobs = 1
    rows: list[dict[str, Any]] = []
    tasks: list[dict[str, Any]] = []
    for row in rows_in:
        if not isinstance(row, dict):
            continue
        detail = _load_json(Path(str(row["detail_json"])))
        result = detail.get("result", {})
        if not isinstance(result, dict):
            raise ValueError(f"{row['detail_json']}: missing result object")
        recorded_builder = str(result.get("profile_builder", "auto"))
        tasks.append(
            {
                "N": int(row["N"]),
                "K": int(row["K"]),
                "detail_json": str(row["detail_json"]),
                "raw_archive": str(args.raw_archive),
                "frame": args.frame,
                "frame_limit": int(args.frame_limit),
                "tail_eta": float(args.tail_eta),
                "zero_eps": float(args.zero_eps),
                "triad_sample_limit": int(args.triad_sample_limit),
                "profile_builder": recorded_builder if str(args.profile_builder) == "auto" else str(args.profile_builder),
                "streaming_shell_threshold": int(args.streaming_shell_threshold),
                "lobpcg_tol": float(args.lobpcg_tol),
                "lobpcg_maxiter": int(args.lobpcg_maxiter),
                "block_size": int(args.block_size),
                "generalized_mass_shift": float(args.generalized_mass_shift),
                "kn_backend": str(args.kn_backend),
            }
        )
    log("prepared tasks", row_count=len(tasks), jobs=jobs, backend=str(args.kn_backend))
    if jobs == 1:
        for task in tasks:
            row_payload, trace = _compute_row(task)
            rows.append(row_payload)
            for entry in trace:
                log(entry["message"], **{k: v for k, v in entry.items() if k not in {"at", "message"}})
            import sys
            sys.stdout.flush()
    else:
        with concurrent.futures.ProcessPoolExecutor(max_workers=jobs) as executor:
            futures = [executor.submit(_compute_row, task) for task in tasks]
            for future in concurrent.futures.as_completed(futures):
                row_payload, trace = future.result()
                rows.append(row_payload)
                for entry in trace:
                    log(entry["message"], **{k: v for k, v in entry.items() if k not in {"at", "message"}})
    rows.sort(key=lambda item: int(item["N"]))
    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "status": "ok",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "scaling_summary": str(args.scaling_summary),
        "raw_archive": str(args.raw_archive),
        "row_count": int(len(rows)),
        "rows": rows,
        "analysis_read": _analysis_read(rows),
        "log_entries": log_entries,
        "started_at": started_at,
        "finished_at": _iso_now(),
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }
    summary_json = args.output_dir / "summary.json"
    summary_md = args.output_dir / "summary.md"
    summary_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    summary_md.write_text(_markdown(payload), encoding="utf-8")
    log("wrote cross-shell block decomposition artifacts", summary_json=str(summary_json), summary_md=str(summary_md))
    payload["finished_at"] = _iso_now()
    payload["elapsed_ms"] = round((time.perf_counter() - started) * 1000.0, 3)
    summary_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
