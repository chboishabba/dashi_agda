#!/usr/bin/env python3
"""Symbolic Schur-complement audit of M = L_neg,cross − (1/9)L_abs,cross.

For each forced-tail row this script:
  1. Builds the seam-block matrices from the edge list.
  2. Partitions the block into G = {shell 1} and C = {shells N-1, N}.
  3. Extracts M_GG, M_GC, M_CC.
  4. Audits the Schur complement
       S_C = M_CC − M_CG M_GG⁻¹ M_GC
     using dense `eigh` only on small C-blocks and `LinearOperator` + `eigsh`
     on larger ones.

This is a candidate-only proof-target artifact. It records observed PSD/nullity
patterns and null-mode diagnostics; it does not prove Gate 1.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
from scipy.linalg import cho_factor, cho_solve, eigh
from scipy.sparse.linalg import LinearOperator, eigsh

from ns_triad_frame_stability_scan import (
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_ZERO_EPS,
    _frame_indices,
    _load_raw_bundle,
)
from ns_triad_kn_cross_shell_block_decomposition import (
    _build_profile_for_row,
)
from ns_triad_kn_matrix_free_operator import (
    MatrixFreeKNProfile,
)

SCRIPT_NAME = "scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py"
CONTRACT = "ns_triad_kn_cross_shell_schur_symbolic_audit"
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_cross_shell_schur_audit_20260626"
)

C0 = 1.0 / 9.0

# C-block size above which we skip dense eigensolves and use `eigsh`.
DENSE_SCHUR_THRESHOLD = 3500


def _build_block_matrices_dense(
    profile: MatrixFreeKNProfile,
    block_indices: np.ndarray,
    c0: float = C0,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    """Build dense M = L_neg − c0·L_abs restricted to the block.

    Uses vectorized construction (no Python loops over edges).

    Returns (M_dense, Ln_dense, La_dense, info).
    """
    n = len(block_indices)

    left = profile.edge_left.astype(np.int64)
    right = profile.edge_right.astype(np.int64)
    w_neg = profile.weights_neg
    w_abs = profile.weights_abs

    # Build O(1) membership/local-index arrays once; avoids Python-loop edge scans.
    in_block = np.zeros(profile.mode_count, dtype=bool)
    in_block[np.asarray(block_indices, dtype=np.int64)] = True
    local_of_orig = np.full(profile.mode_count, -1, dtype=np.int64)
    local_of_orig[np.asarray(block_indices, dtype=np.int64)] = np.arange(n, dtype=np.int64)

    # Which edges touch the block?
    l_in = in_block[left]
    r_in = in_block[right]
    touches = l_in | r_in

    e_left = left[touches]
    e_right = right[touches]
    e_wn = w_neg[touches]
    e_wa = w_abs[touches]
    e_l_in = l_in[touches]
    e_r_in = r_in[touches]

    # Internal edges (both ends in block)
    both = e_l_in & e_r_in
    nip = int(np.sum(both))
    # Boundary edges (exactly one end in block)
    bound = e_l_in != e_r_in
    nbp = int(np.sum(bound))

    # -- Diagonal via bincount (vectorized over vertices) --
    diag_n = np.zeros(n, dtype=np.float64)
    diag_a = np.zeros(n, dtype=np.float64)
    for side_orig, side_in in ((e_left, e_l_in), (e_right, e_r_in)):
        locs = local_of_orig[side_orig[side_in]]
        np.add.at(diag_n, locs, e_wn[side_in])
        np.add.at(diag_a, locs, e_wa[side_in])

    # -- Off-diagonal COO entries for internal edges --
    int_left = e_left[both]
    int_right = e_right[both]
    int_wn = e_wn[both]
    int_wa = e_wa[both]
    loc_l = local_of_orig[int_left]
    loc_r = local_of_orig[int_right]

    rows_n = np.concatenate([np.arange(n, dtype=np.int64), loc_l, loc_r])
    cols_n = np.concatenate([np.arange(n, dtype=np.int64), loc_r, loc_l])
    vals_n = np.concatenate([diag_n, -int_wn, -int_wn])

    rows_a = np.concatenate([np.arange(n, dtype=np.int64), loc_l, loc_r])
    cols_a = np.concatenate([np.arange(n, dtype=np.int64), loc_r, loc_l])
    vals_a = np.concatenate([diag_a, -int_wa, -int_wa])

    from scipy.sparse import coo_matrix
    Ln = coo_matrix((vals_n, (rows_n, cols_n)), shape=(n, n)).toarray()
    La = coo_matrix((vals_a, (rows_a, cols_a)), shape=(n, n)).toarray()
    M = Ln - c0 * La

    info = {
        "n_modes": n,
        "n_edges_touching": int(len(e_left)),
        "n_edges_internal": nip,
        "n_edges_boundary": nbp,
    }
    return M, Ln, La, info


def _extract_blocks(
    M_dense: np.ndarray,
    g_indices_local: np.ndarray,
    c_indices_local: np.ndarray,
) -> dict[str, np.ndarray]:
    """Extract M_GG, M_GC, M_CC given local index arrays."""
    ng = len(g_indices_local)
    nc = len(c_indices_local)
    if ng > 0 and nc > 0:
        M_GG = M_dense[np.ix_(g_indices_local, g_indices_local)]
        M_GC = M_dense[np.ix_(g_indices_local, c_indices_local)]
        M_CC = M_dense[np.ix_(c_indices_local, c_indices_local)]
    elif ng > 0:
        M_GG = M_dense[np.ix_(g_indices_local, g_indices_local)]
        M_GC = np.zeros((ng, 0), dtype=np.float64)
        M_CC = np.zeros((0, 0), dtype=np.float64)
    elif nc > 0:
        M_GG = np.zeros((0, 0), dtype=np.float64)
        M_GC = np.zeros((0, nc), dtype=np.float64)
        M_CC = M_dense[np.ix_(c_indices_local, c_indices_local)]
    else:
        M_GG = np.zeros((0, 0), dtype=np.float64)
        M_GC = np.zeros((0, 0), dtype=np.float64)
        M_CC = np.zeros((0, 0), dtype=np.float64)
    return {"M_GG": M_GG, "M_GC": M_GC, "M_CC": M_CC}


def _sym_eigvals(mat: np.ndarray) -> np.ndarray:
    """Symmetric eigenvalues only."""
    sym = 0.5 * (mat + mat.T)
    try:
        return eigh(sym, driver="ev", eigvals_only=True)
    except Exception:
        return eigh(sym, driver="evd", eigvals_only=True)


def _block_stats(label: str, mat: np.ndarray, tol: float = 1.0e-10) -> dict[str, Any]:
    """Statistics for a symmetric block matrix."""
    n = mat.shape[0]
    if n == 0:
        return {"label": label, "n": 0, "rank": 0, "nullity": 0,
                "lambda_min": None, "lambda_max": None, "norm": 0.0, "psd_gap": None}
    evals = _sym_eigvals(mat)
    rank = int(np.sum(evals > tol))
    return {
        "label": label, "n": n, "rank": rank, "nullity": n - rank,
        "lambda_min": float(evals[0]), "lambda_max": float(evals[-1]),
        "norm": max(abs(evals[0]), abs(evals[-1])),
        "psd_gap": float(evals[0]),
    }


def _worst_eigenvector_support(
    mat: np.ndarray,
    shell_levels_subset: np.ndarray,
    tol: float = 1.0e-12,
) -> dict[str, Any]:
    """Eigenvector corresponding to the smallest eigenvalue of M_CC, by shell."""
    n = mat.shape[0]
    if n == 0:
        return {"support": {}, "lambda_min": None}
    sym = 0.5 * (mat + mat.T)
    try:
        evals, evecs = eigh(sym, driver="evr")
    except Exception:
        try:
            evals, evecs = eigh(sym, driver="evd")
        except Exception:
            return {"support": {}, "lambda_min": None, "error": "eigh_failed"}
    worst_idx = int(np.argmin(evals))
    worst_vec = np.asarray(evecs[:, worst_idx], dtype=np.float64)
    worst_lambda = float(evals[worst_idx])
    norm_sq = float(np.sum(worst_vec ** 2))
    support = {}
    if norm_sq > tol:
        frac = (worst_vec ** 2) / norm_sq
        for sl in sorted({int(v) for v in shell_levels_subset}):
            mask = shell_levels_subset == sl
            support[str(sl)] = float(np.sum(frac[mask]))
    return {"support": support, "lambda_min": worst_lambda, "norm_sq": norm_sq}


def _shell_support_from_vector(
    vec: np.ndarray,
    shell_levels_subset: np.ndarray,
    tol: float = 1.0e-12,
) -> dict[str, Any]:
    """Mass fraction of a vector grouped by shell."""
    norm_sq = float(np.sum(np.asarray(vec, dtype=np.float64) ** 2))
    support: dict[str, float] = {}
    if norm_sq <= tol:
        return {"support": support, "norm_sq": norm_sq}
    frac = (np.asarray(vec, dtype=np.float64) ** 2) / norm_sq
    for sl in sorted({int(v) for v in shell_levels_subset}):
        mask = shell_levels_subset == sl
        support[str(sl)] = float(np.sum(frac[mask]))
    return {"support": support, "norm_sq": norm_sq}


def _lowest_modes(
    mat: np.ndarray,
    *,
    k: int = 3,
    dense_threshold: int = DENSE_SCHUR_THRESHOLD,
    tol: float = 1.0e-12,
    maxiter: int = 10000,
) -> tuple[np.ndarray, np.ndarray, str]:
    """Return the lowest `k` eigenpairs of a symmetric matrix.

    Uses dense `eigh` on smaller blocks and `LinearOperator` + `eigsh` on
    larger blocks. The matrix is symmetrized once up front.
    """
    sym = np.asarray(0.5 * (mat + mat.T), dtype=np.float64)
    n = int(sym.shape[0])
    if n == 0:
        return np.zeros(0, dtype=np.float64), np.zeros((0, 0), dtype=np.float64), "empty"
    if n == 1:
        return np.asarray([float(sym[0, 0])], dtype=np.float64), np.asarray([[1.0]], dtype=np.float64), "dense"

    k_use = max(1, min(int(k), n - 1))
    if n <= dense_threshold:
        try:
            evals, evecs = eigh(sym, driver="evr", subset_by_index=[0, k_use - 1])
        except Exception:
            evals, evecs = eigh(sym, driver="evd", subset_by_index=[0, k_use - 1])
        return np.asarray(evals, dtype=np.float64), np.asarray(evecs, dtype=np.float64), "dense"

    def _matvec(x: np.ndarray) -> np.ndarray:
        return sym @ x

    op = LinearOperator((n, n), matvec=_matvec, dtype=np.float64)
    evals, evecs = eigsh(op, k=k_use, which="SA", tol=tol, maxiter=maxiter)
    order = np.argsort(evals)
    return np.asarray(evals[order], dtype=np.float64), np.asarray(evecs[:, order], dtype=np.float64), "eigsh"


def _schur_matrix_free_bottom_eigs(
    M_CC: np.ndarray,
    M_GC: np.ndarray,
    M_GG_chol: tuple,
    nc: int,
    k: int = 3,
    tol: float = 1.0e-10,
    maxiter: int = 4000,
) -> tuple[np.ndarray, np.ndarray]:
    """Bottom-k eigenpairs of S_C = M_CC - M_GC.T @ M_GG⁻¹ @ M_GC via matrix-free eigsh.

    M_CC is dense (nc×nc, already in memory). M_GC is dense (ng×nc).
    M_GG_chol is the scipy.linalg.cho_factor output. S_C is never materialised.
    The matvec cost is O(nc²) for the M_CC @ x term plus O(ng·nc) for the correction.
    """
    def _matvec(x: np.ndarray) -> np.ndarray:
        Ax = M_CC @ x                        # dense: O(nc²)
        rhs = M_GC @ x                       # (ng,) — cheap
        sol = cho_solve(M_GG_chol, rhs)      # (ng,) — trivial (ng=26)
        return Ax - M_GC.T @ sol             # (nc,)

    op = LinearOperator((nc, nc), matvec=_matvec, dtype=np.float64)
    k_use = min(k, nc - 1)
    raw_eigs, raw_vecs = eigsh(op, k=k_use, which="SA", tol=tol, maxiter=maxiter)
    idx = np.argsort(raw_eigs)
    return raw_eigs[idx], raw_vecs[:, idx]


def _null_vector_diagnostics(
    v0: np.ndarray,
    c_shell_levels: np.ndarray,
    degree: np.ndarray | None = None,
    tol: float = 1.0e-14,
) -> dict[str, Any]:
    """Cosine correlations of the S_C near-null vector with structural indicator vectors.

    Reports:
      corr_constant, corr_shell_<sl>, corr_shell_balance,
      corr_sqrt_degree, corr_inv_degree, corr_degree_weighted_balance,
      shell_mass (squared-weight fraction per shell).
    """
    v = np.asarray(v0, dtype=np.float64)
    norm_v = float(np.linalg.norm(v))
    if norm_v < tol:
        return {"error": "zero_vector"}

    shells = sorted({int(s) for s in c_shell_levels})
    n = len(v)

    def _corr(w: np.ndarray) -> float:
        norm_w = float(np.linalg.norm(w))
        return float("nan") if norm_w < tol else float(np.dot(v, w) / (norm_v * norm_w))

    diag: dict[str, Any] = {}
    diag["corr_constant"] = _corr(np.ones(n, dtype=np.float64))

    shell_inds: dict[str, np.ndarray] = {}
    for sl in shells:
        ind = (c_shell_levels == sl).astype(np.float64)
        diag[f"corr_shell_{sl}"] = _corr(ind)
        shell_inds[str(sl)] = ind

    diag["shell_mass"] = {
        str(sl): float(np.sum((v / norm_v) ** 2 * (c_shell_levels == sl)))
        for sl in shells
    }

    if len(shells) >= 2:
        sl_lo, sl_hi = shells[0], shells[-1]
        balance = shell_inds[str(sl_lo)] - shell_inds[str(sl_hi)]
        diag["corr_shell_balance"] = _corr(balance)
    else:
        balance = None

    if degree is not None:
        deg = np.asarray(degree, dtype=np.float64)
        diag["corr_sqrt_degree"] = _corr(np.sqrt(np.clip(deg, 0.0, None)))
        diag["corr_inv_degree"] = _corr(np.where(deg > tol, 1.0 / deg, 0.0))
        if balance is not None:
            diag["corr_degree_weighted_balance"] = _corr(deg * balance)

    return diag


def _audit_row(
    bundle: Any,
    snapshot: int,
    n: int,
    cutoff: int,
    eta: float,
    zero_eps: float,
    triad_sample_limit: int,
    profile_builder: str,
    streaming_shell_threshold: int,
    dense_schur_threshold: int = DENSE_SCHUR_THRESHOLD,
) -> dict[str, Any]:
    """Run the full Schur audit for one (N, K) row."""
    t0 = time.time()
    print(f"\n{'='*60}")
    print(f"  N={n}, K={cutoff}, η={eta:.3f}, builder={profile_builder}")
    print(f"{'='*60}")

    profile, probability = _build_profile_for_row(
        bundle=bundle,
        snapshot=snapshot,
        shell=n,
        cutoff=cutoff,
        eta=eta,
        zero_eps=zero_eps,
        triad_sample_limit=triad_sample_limit,
        profile_builder=profile_builder,
        streaming_shell_threshold=streaming_shell_threshold,
    )
    print(f"  Modes: {profile.mode_count}, Edges: {len(profile.edge_left)}")

    shell_levels = np.asarray(profile.shell_levels, dtype=np.float64)
    block_shells = (1, cutoff, n)
    block_mask = np.isin(shell_levels.astype(np.int64), np.asarray(block_shells, dtype=np.int64))
    block_indices = np.flatnonzero(block_mask)
    print(f"  Seam block: {len(block_indices)} modes (shells {block_shells})")

    # Partition: G = {shell 1}, C = {shells cutoff, n}
    g_mask = shell_levels == 1.0
    g_in_block = g_mask & block_mask
    c_in_block = block_mask & ~g_in_block
    g_indices = np.flatnonzero(g_in_block)
    c_indices = np.flatnonzero(c_in_block)
    ng = len(g_indices)
    nc = len(c_indices)
    print(f"  G (shell 1): {ng} modes")
    print(f"  C (shells {cutoff},{n}): {nc} modes")

    # Build dense block matrices
    print(f"  Building dense block matrices...", end=" ", flush=True)
    M_block, Ln_block, La_block, blk_info = _build_block_matrices_dense(
        profile, block_indices, c0=C0,
    )
    print(f"done. ({blk_info['n_modes']}×{blk_info['n_modes']}, "
          f"{blk_info['n_edges_touching']} edges, {blk_info['n_edges_internal']} internal)")

    # Map original indices to local positions in the reordered block
    all_ordered = np.concatenate([g_indices, c_indices])
    local_of_orig = {int(orig): loc for loc, orig in enumerate(all_ordered)}
    perm = np.array([local_of_orig[int(orig)] for orig in block_indices], dtype=np.int64)
    M_reord = M_block[perm][:, perm]

    g_local = np.arange(ng, dtype=np.int64)
    c_local = np.arange(ng, ng + nc, dtype=np.int64)
    blocks = _extract_blocks(M_reord, g_local, c_local)

    # Statistics for block submatrices
    stats_gg = _block_stats("M_GG", blocks["M_GG"])
    gc_norm = float(np.linalg.norm(blocks["M_GC"]))
    if nc <= dense_schur_threshold:
        stats_cc = _block_stats("M_CC", blocks["M_CC"])
        mcc_eval_method = "dense"
        mcc_bottom_eigs = None
        mcc_bottom_vec = None
    else:
        mcc_eigs, mcc_vecs, mcc_eval_method = _lowest_modes(
            blocks["M_CC"], k=3, dense_threshold=dense_schur_threshold
        )
        mcc_bottom_eigs = [float(v) for v in mcc_eigs]
        mcc_bottom_vec = np.asarray(mcc_vecs[:, 0], dtype=np.float64)
        nullity_estimate = int(np.sum(np.abs(mcc_eigs) <= 1.0e-10))
        stats_cc = {
            "label": "M_CC",
            "n": nc,
            "rank": None,
            "nullity": None,
            "nullity_estimate": nullity_estimate,
            "lambda_min": float(mcc_eigs[0]),
            "lambda_max": None,
            "norm": None,
            "psd_gap": float(mcc_eigs[0]),
            "bottom_eigs": mcc_bottom_eigs,
            "evaluation_method": mcc_eval_method,
        }

    print(f"  M_GG: n={stats_gg['n']}, rank={stats_gg['rank']}, "
          f"‖·‖={stats_gg['norm']:.6e}, λ_min={stats_gg['lambda_min']:.6e}")
    print(f"  ‖M_GC‖ = {gc_norm:.6e}")

    c_shell_levels = shell_levels[c_indices]
    M_GG = blocks["M_GG"]
    M_GC = blocks["M_GC"]
    M_CC = blocks["M_CC"]

    # Schur complement S_C = M_CC − M_CG M_GG⁻¹ M_GC
    # For nc ≤ dense_schur_threshold: full eigh (exact, O(nc³)).
    # For nc >  dense_schur_threshold: matrix-free eigsh (bottom-k only, avoids O(nc³)).
    sc_ok = False
    stats_sc: dict[str, Any] = {"label": "S_C", "n": nc, "rank": None, "nullity": None,
                                 "lambda_min": None, "lambda_max": None, "norm": None, "psd_gap": None}
    correction_norm: float | None = None
    sc_null_vec: np.ndarray | None = None
    null_vector_diag: dict[str, Any] | None = None
    wsp_sc: dict[str, Any] = {"support": {}, "lambda_min": None}

    try:
        M_GG_sym = 0.5 * (M_GG + M_GG.T)
        M_GG_chol = cho_factor(M_GG_sym)              # 26×26 — trivial
        M_GG_inv_M_GC = cho_solve(M_GG_chol, M_GC)   # (ng, nc)
        correction = M_GC.T @ M_GG_inv_M_GC           # (nc, nc), rank ng
        correction_norm = float(np.linalg.norm(correction))
        sc_ok = True
    except Exception as _exc:
        print(f"  M_GG Cholesky failed: {_exc}")

    print(f"  M_CC λ_min: {stats_cc['lambda_min']:.6e}")

    if sc_ok:
        naive_bound = (gc_norm ** 2) / max(stats_gg["lambda_min"], 1.0e-300)
        print(f"  ‖M_CG M_GG⁻¹ M_GC‖ = {correction_norm:.6e}  (naive bound: {naive_bound:.6e})")

        if nc <= dense_schur_threshold:
            # Dense eigh path — exact, used for N≤10
            print(f"  Computing S_C (dense eigh, n={nc})...", end=" ", flush=True)
            S_C_dense = M_CC - correction
            stats_sc = _block_stats("S_C", S_C_dense)
            # Bottom eigenvector for null-mode diagnostics
            sym_sc = 0.5 * (S_C_dense + S_C_dense.T)
            _k_diag = min(5, nc - 1)
            try:
                _evals_d, _evecs_d = eigh(sym_sc, driver="evr",
                                          subset_by_index=[0, _k_diag])
                sc_null_vec = np.asarray(_evecs_d[:, 0], dtype=np.float64)
            except Exception:
                sc_null_vec = None
            wsp_sc = _worst_eigenvector_support(S_C_dense, c_shell_levels)
            print("done.")
        else:
            # Matrix-free eigsh path — avoids materialising S_C for large nc
            print(f"  Computing S_C bottom eigenvalues (matrix-free eigsh, n={nc})...",
                  end=" ", flush=True)
            try:
                _mf_eigs, _mf_vecs = _schur_matrix_free_bottom_eigs(
                    M_CC, M_GC, M_GG_chol, nc, k=3, tol=1.0e-10
                )
                sc_null_vec = np.asarray(_mf_vecs[:, 0], dtype=np.float64)
                _lmin = float(_mf_eigs[0])
                _nullity = int(np.sum(np.abs(_mf_eigs) <= 1.0e-10))
                _shell_mass = {
                    str(sl): float(np.sum(
                        (sc_null_vec / max(np.linalg.norm(sc_null_vec), 1e-300)) ** 2
                        * (c_shell_levels == sl)
                    ))
                    for sl in sorted({int(s) for s in c_shell_levels})
                }
                stats_sc = {
                    "label": "S_C",
                    "n": nc,
                    "rank": nc - _nullity,
                    "nullity": _nullity,
                    "nullity_estimate": _nullity,
                    "lambda_min": _lmin,
                    "lambda_max": None,
                    "norm": None,
                    "psd_gap": _lmin,
                    "bottom_eigs": [float(v) for v in _mf_eigs],
                    "evaluation_method": "eigsh",
                }
                wsp_sc = {"support": _shell_mass, "lambda_min": _lmin}
                print("done.")
                print(f"  S_C bottom eigs: {[f'{v:.6e}' for v in _mf_eigs]}")
            except Exception as _exc:
                print(f"eigsh failed: {_exc}")
                sc_ok = False

        if sc_ok and stats_sc.get("psd_gap") is not None:
            sc_psd_gap = stats_sc["psd_gap"]
            verdict = "schur_psd" if sc_psd_gap >= -1.0e-8 else "schur_indefinite"
            nullity_str = stats_sc.get("nullity")
            print(f"  S_C: n={stats_sc['n']}, rank={stats_sc.get('rank')}, "
                  f"nullity={nullity_str}, λ_min={stats_sc['lambda_min']:.6e}")
            print(f"  S_C PSD gap: {sc_psd_gap:.6e} → {verdict}")
        else:
            verdict = "schur_unresolved" if sc_ok else "schur_unresolved"
    else:
        verdict = "schur_unresolved"
        print("  S_C: could not compute (M_GG Cholesky failed)")

    # Worst M_CC eigenvector shell support
    if mcc_bottom_vec is not None:
        wsp_mcc = {
            "support": _shell_support_from_vector(mcc_bottom_vec, c_shell_levels)["support"],
            "lambda_min": stats_cc["lambda_min"],
            "bottom_eigs": mcc_bottom_eigs,
            "evaluation_method": mcc_eval_method,
        }
    else:
        wsp_mcc = _worst_eigenvector_support(blocks["M_CC"], c_shell_levels)
    print(f"  Worst M_CC eigenvector λ={wsp_mcc['lambda_min']:.6e}, "
          f"shell support: {wsp_mcc['support']}")
    if wsp_sc.get("lambda_min") is not None:
        print(f"  Worst S_C eigenvector λ={wsp_sc['lambda_min']:.6e}, "
              f"shell support: {wsp_sc['support']}")

    # Null-vector diagnostics: correlations with structural indicator vectors
    if sc_ok and sc_null_vec is not None:
        # Degree of C-block nodes in full edge list (vectorised, O(E))
        _c_idx_map = np.full(profile.mode_count, -1, dtype=np.int64)
        _c_idx_map[c_indices] = np.arange(nc, dtype=np.int64)
        _el_pos = _c_idx_map[profile.edge_left]
        _er_pos = _c_idx_map[profile.edge_right]
        _deg_c = np.zeros(nc, dtype=np.float64)
        np.add.at(_deg_c, _el_pos[_el_pos >= 0], 1.0)
        np.add.at(_deg_c, _er_pos[_er_pos >= 0], 1.0)
        null_vector_diag = _null_vector_diagnostics(sc_null_vec, c_shell_levels,
                                                     degree=_deg_c)
        print(f"  Null-mode corr(constant)={null_vector_diag.get('corr_constant', '—'):.4f}, "
              f"corr(balance)={null_vector_diag.get('corr_shell_balance', '—'):.4f}, "
              f"corr(sqrt_deg)={null_vector_diag.get('corr_sqrt_degree', '—'):.4f}")

    elapsed = time.time() - t0
    return {
        "N": n,
        "K": cutoff,
        "eta": eta,
        "mode_count": profile.mode_count,
        "edge_count": int(len(profile.edge_left)),
        "block_size": int(len(block_indices)),
        "G_size": ng,
        "C_size": nc,
        "M_GG": stats_gg,
        "M_GC_norm": gc_norm,
        "M_CC": stats_cc,
        "M_CC_worst_eigenvector_support": wsp_mcc,
        "S_C": stats_sc if sc_ok else None,
        "correction_norm": correction_norm,
        "S_C_worst_eigenvector_support": wsp_sc,
        "null_vector_diagnostics": null_vector_diag,
        "schur_complement_ok": sc_ok,
        "verdict": verdict,
        "elapsed_seconds": round(elapsed, 2),
        "c0": C0,
    }


def _analyze(results: list[dict[str, Any]]) -> str:
    if not results:
        return "No rows."
    lines = [
        "## Schur Audit Summary",
        "",
        "| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | corr(balance) | Verdict |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|",
    ]
    for r in results:
        sc = r.get("S_C") or {}
        bottom_eigs = sc.get("bottom_eigs") or []
        eig_strs = []
        for i in range(3):
            if i < len(bottom_eigs):
                eig_strs.append(f"{bottom_eigs[i]:.6e}")
            else:
                eig_strs.append("—")
        sc_lmin = eig_strs[0]
        sc_nullity = str(sc.get("nullity_estimate", sc.get("nullity", "—")))
        nvd = r.get("null_vector_diagnostics") or {}
        bal = nvd.get("corr_shell_balance")
        bal_str = f"{bal:.4f}" if bal is not None and not (isinstance(bal, float) and math.isnan(bal)) else "—"
        lines.append(
            f"| {r['N']} | {r['block_size']} | {r['G_size']} | {r['C_size']} | "
            f"{r['M_CC']['lambda_min']:.6e} | {eig_strs[0]} | {eig_strs[1]} | {eig_strs[2]} | "
            f"{sc_nullity} | {bal_str} | {r['verdict']} |"
        )
    lines.append("")
    for r in results:
        sc = r.get("S_C")
        if sc and sc['lambda_min'] is not None:
            bottom_eigs = sc.get("bottom_eigs") or []
            eig_desc = ", ".join(f"λ{i}={v:.6e}" for i, v in enumerate(bottom_eigs[:3]))
            lines.append(
                f"N={r['N']}: {eig_desc}, nullity_est={sc.get('nullity_estimate', sc.get('nullity'))}, "
                f"eval={sc.get('evaluation_method', 'dense')}"
            )
    gc_norms = [r["M_GC_norm"] for r in results]
    lines.append(f"\nM_GC norms: {', '.join(f'{v:.2e}' for v in gc_norms)}")
    verdicts = {r["verdict"] for r in results}
    lines.append(f"Verdicts: {sorted(verdicts)}")
    psd_observed = all(r.get("S_C") and (r["S_C"].get("lambda_min") is not None)
                       and (r["S_C"]["lambda_min"] >= -1.0e-8) for r in results)
    nullity_one_observed = all(r.get("S_C") and (r["S_C"].get("nullity_estimate", r["S_C"].get("nullity")) == 1)
                               for r in results)
    if psd_observed and nullity_one_observed:
        lines.append("Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.")
    else:
        lines.append("Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: OPEN.")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--zero-eps", type=float, default=float(DEFAULT_ZERO_EPS))
    parser.add_argument("--eta", type=float, default=0.25)
    parser.add_argument("--triad-sample-limit", type=int, default=0)
    parser.add_argument("--profile-builder", choices=["auto", "streaming", "framesurface"], default="auto")
    parser.add_argument("--streaming-shell-threshold", type=int, default=10)
    parser.add_argument("--shells", type=int, nargs="+", default=[6, 8, 10, 12])
    parser.add_argument("--dense-schur-threshold", type=int, default=DENSE_SCHUR_THRESHOLD,
                        help="nc above which matrix-free eigsh replaces dense eigh for S_C")
    args = parser.parse_args()

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    bundle = _load_raw_bundle(Path(args.raw_archive), [])
    snapped = _frame_indices(bundle.frame_count, frame=None, frame_limit=1)
    snapshot = int(snapped[0][1] if isinstance(snapped[0], tuple) else snapped[0])

    results = []
    for n in sorted(args.shells):
        cutoff = n - 1
        builder = args.profile_builder
        result = _audit_row(
            bundle=bundle,
            snapshot=snapshot,
            n=n,
            cutoff=cutoff,
            eta=args.eta,
            zero_eps=args.zero_eps,
            triad_sample_limit=args.triad_sample_limit,
            profile_builder=builder,
            streaming_shell_threshold=args.streaming_shell_threshold,
            dense_schur_threshold=args.dense_schur_threshold,
        )
        results.append(result)

    summary_text = _analyze(results)
    psd_verified = all(
        r["schur_complement_ok"]
        and (r.get("S_C") is not None)
        and (r["S_C"].get("lambda_min") is not None)
        and (r["S_C"]["lambda_min"] >= -1.0e-8)
        for r in results
    )
    nullity_one_observed = all(
        r["schur_complement_ok"]
        and (r.get("S_C") is not None)
        and (r["S_C"].get("nullity_estimate", r["S_C"].get("nullity")) == 1)
        for r in results
    )

    payload = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "schema_version": "1.0.0",
        "c0": C0,
        "rows": results,
        "analysis_text": summary_text,
        "candidate_only": True,
        "theorem_promoted": False,
        "gate1_closed": False,
        "gate1_supported_at_tested_shells": bool(psd_verified and nullity_one_observed),
        "gate1_target": "S_C = M_CC − M_CG M_GG⁻¹ M_GC ⪰ 0 and dim ker S_C = 1",
        "schurComplementPsdVerified": bool(psd_verified),
        "schurComplementNullityOneObserved": bool(nullity_one_observed),
        "schurComplementMatrixFreeAuditInstalled": True,
        "schurComplementPsdProved": False,
        "schurNullModeIdentified": False,
        "schurNullModeFactorizationProved": False,
    }

    json_path = output_dir / "schur_audit.json"
    json_path.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")
    print(f"\nJSON → {json_path}")

    md_lines = [
        "# NS Triad K_N Cross-Shell Schur Symbolic Audit",
        "",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- gate1 closed: `{payload['gate1_closed']}`",
        f"- gate1 supported at tested shells: `{payload['gate1_supported_at_tested_shells']}`",
        "",
        summary_text,
    ]
    md_path = output_dir / "schur_audit.md"
    md_path.write_text("\n".join(md_lines), encoding="utf-8")
    print(f"MD  → {md_path}")
    print(f"\n{summary_text}")


if __name__ == "__main__":
    main()
