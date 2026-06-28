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
import importlib.util
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from scipy.linalg import cho_factor, cho_solve, eigh
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from scipy.sparse.linalg import LinearOperator, eigsh, lobpcg

from ns_triad_frame_stability_scan import (
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_ZERO_EPS,
    _frame_indices,
    _frame_velocity,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_triad_constrained_adversarial_fork_optimizer import (
    _cube_modes,
    _shell_levels,
)
from ns_triad_kn_cross_shell_block_decomposition import (
    _build_profile_for_row,
)
from ns_triad_kn_matrix_free_operator import (
    MatrixFreeKNProfile,
    profile_from_weight_matrices,
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

SCRIPT_NAME = "scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py"
CONTRACT = "ns_triad_kn_cross_shell_schur_symbolic_audit"
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_cross_shell_schur_audit_20260626"
)

C0 = 1.0 / 9.0

# C-block size above which we skip dense eigensolves and use `eigsh`.
DENSE_SCHUR_THRESHOLD = 3500
DEFAULT_DOMINATION_CHUNK_SIZE = 192
DEFAULT_DOMINATION_EPS = 1.0e-8
CHECKPOINT_SCHEMA_VERSION = "1.0.0"


@dataclass(frozen=True)
class _ChunkedSignedLaplacian:
    kind: str
    degree: np.ndarray
    row_chunk: int


@dataclass(frozen=True)
class _RestrictedBackend:
    name: str
    good_mv: Any
    bad_mv: Any
    info: dict[str, Any]
    close: Any = lambda: None


def _checkpoint_paths(base_path: Path) -> tuple[Path, Path]:
    path_str = str(base_path)
    if path_str.endswith(".core.npz"):
        stem = Path(path_str[: -len(".core.npz")])
    elif path_str.endswith(".matrices.npz"):
        stem = Path(path_str[: -len(".matrices.npz")])
    elif path_str.endswith(".npz"):
        stem = Path(path_str[: -len(".npz")])
    else:
        stem = base_path
    return stem.with_suffix(".core.npz"), stem.with_suffix(".matrices.npz")


def _row_partial_json_path(base_path: Path, n: int) -> Path:
    if base_path.suffix == ".json":
        stem = base_path.with_suffix("")
    else:
        stem = base_path
    return stem.parent / f"{stem.name}.N{n}.partial.json"


def _row_checkpoint_base_path(base_path: Path, n: int) -> Path:
    if base_path.suffix == ".npz":
        stem = base_path.with_suffix("")
    else:
        stem = base_path
    return stem.parent / f"{stem.name}.N{n}"


def _json_ready(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): _json_ready(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_json_ready(v) for v in value]
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, np.generic):
        return value.item()
    return value


def _write_partial_row_receipt(path: Path, result: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_json_ready(result), indent=2), encoding="utf-8")


def _signed_split_from_schur(S_C: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    total = np.asarray(S_C, dtype=np.float64)
    good_weights = np.maximum(-total, 0.0)
    bad_weights = np.maximum(total, 0.0)
    diag = np.arange(total.shape[0], dtype=np.int64)
    good_weights[diag, diag] = 0.0
    bad_weights[diag, diag] = 0.0
    L_good = np.diag(np.sum(good_weights, axis=1)) - good_weights
    L_bad = np.diag(np.sum(bad_weights, axis=1)) - bad_weights
    Q = 2.0 * L_good - 3.0 * L_bad
    return L_good, L_bad, Q


def _write_schur_checkpoint(
    *,
    base_path: Path,
    n: int,
    cutoff: int,
    M_CC: np.ndarray,
    correction: np.ndarray,
    c_shell_levels: np.ndarray,
    c_mode_keys: list[tuple[int, int, int]],
    result: dict[str, Any],
) -> tuple[Path, Path]:
    core_path, matrices_path = _checkpoint_paths(base_path)
    core_path.parent.mkdir(parents=True, exist_ok=True)
    matrices_path.parent.mkdir(parents=True, exist_ok=True)

    S_C = np.asarray(M_CC - correction, dtype=np.float64)
    L_good, L_bad, Q = _signed_split_from_schur(S_C)
    mode_key_array = np.asarray(c_mode_keys, dtype=np.int64) if c_mode_keys else np.zeros((0, 3), dtype=np.int64)
    row_pair_diag = result.get("domination_row_pairing_diagnostics") or {}
    full_diag = result.get("domination_ratio_matrix_free_diagnostics") or {}
    rho_vec = np.asarray(full_diag.get("_rho_vec_full", []), dtype=np.float64)
    q_vec = np.asarray(row_pair_diag.get("_q_bottom_vec_full", []), dtype=np.float64)

    np.savez_compressed(
        core_path,
        schema_version=np.asarray(CHECKPOINT_SCHEMA_VERSION),
        contract=np.asarray(CONTRACT),
        N=np.asarray(int(n), dtype=np.int64),
        K=np.asarray(int(cutoff), dtype=np.int64),
        c_shell_levels=np.asarray(c_shell_levels, dtype=np.float64),
        c_mode_keys=mode_key_array,
        rho_vec=rho_vec,
        q_bottom_vec=q_vec,
        result_json=np.asarray(json.dumps(_json_ready(result))),
    )
    np.savez(
        matrices_path,
        M_CC=np.asarray(M_CC, dtype=np.float64),
        correction=np.asarray(correction, dtype=np.float64),
        S_C=S_C,
        L_good=L_good,
        L_bad=L_bad,
        Q=Q,
    )
    return core_path, matrices_path


def _load_schur_checkpoint(base_path: Path) -> dict[str, Any]:
    core_path, matrices_path = _checkpoint_paths(base_path)
    if not core_path.exists():
        raise FileNotFoundError(f"missing checkpoint core file: {core_path}")
    if not matrices_path.exists():
        raise FileNotFoundError(f"missing checkpoint matrices file: {matrices_path}")

    with np.load(core_path, allow_pickle=False) as core_data:
        schema_version = str(core_data["schema_version"].item())
        contract = str(core_data["contract"].item())
        if contract != CONTRACT:
            raise ValueError(f"checkpoint contract mismatch: expected {CONTRACT}, got {contract}")
        result = json.loads(str(core_data["result_json"].item()))
        payload = {
            "schema_version": schema_version,
            "N": int(core_data["N"].item()),
            "K": int(core_data["K"].item()),
            "c_shell_levels": np.asarray(core_data["c_shell_levels"], dtype=np.float64),
            "c_mode_keys": [
                tuple(int(v) for v in row)
                for row in np.asarray(core_data["c_mode_keys"], dtype=np.int64).tolist()
            ],
            "rho_vec": np.asarray(core_data["rho_vec"], dtype=np.float64),
            "q_bottom_vec": np.asarray(core_data["q_bottom_vec"], dtype=np.float64),
            "result": result,
        }
    with np.load(matrices_path, allow_pickle=False) as mat_data:
        payload.update(
            {
                "M_CC": np.asarray(mat_data["M_CC"], dtype=np.float64),
                "correction": np.asarray(mat_data["correction"], dtype=np.float64),
                "S_C": np.asarray(mat_data["S_C"], dtype=np.float64),
                "L_good": np.asarray(mat_data["L_good"], dtype=np.float64),
                "L_bad": np.asarray(mat_data["L_bad"], dtype=np.float64),
                "Q": np.asarray(mat_data["Q"], dtype=np.float64),
            }
        )
    return payload


def _project_mean_zero(x: np.ndarray) -> np.ndarray:
    vec = np.asarray(x, dtype=np.float64)
    return vec - float(np.mean(vec))


def _lift_one_perp_coords(y: np.ndarray) -> np.ndarray:
    values = np.asarray(y, dtype=np.float64)
    if values.ndim == 1:
        return np.concatenate([values, np.asarray([-float(np.sum(values))], dtype=np.float64)])
    if values.ndim == 2:
        tail = -np.sum(values, axis=0, keepdims=True)
        return np.vstack([values, tail])
    raise ValueError(f"expected vector or matrix reduced coordinate input, got ndim={values.ndim}")


def _compress_one_perp_dual(z: np.ndarray) -> np.ndarray:
    values = np.asarray(z, dtype=np.float64)
    if values.ndim == 1:
        return values[:-1] - values[-1]
    if values.ndim == 2:
        return values[:-1, :] - values[-1:, :]
    raise ValueError(f"expected vector or matrix full-space input, got ndim={values.ndim}")


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


def _c_block_mode_keys(
    bundle: Any,
    snapshot: int,
    n: int,
    c_indices: np.ndarray,
    zero_eps: float,
) -> list[tuple[int, int, int]]:
    u, v, w = _frame_velocity(bundle, snapshot)
    spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
    shell_modes = _cube_modes(spectrum, shell_n=int(n), zero_eps=float(zero_eps))
    return [tuple(int(v) for v in shell_modes[int(index)].key) for index in c_indices]


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


def _schur_row_sum_diagnostics(
    M_CC: np.ndarray,
    M_GC: np.ndarray,
    M_GG_chol: tuple,
) -> dict[str, Any]:
    """Diagnostics for the candidate constant null mode of the Schur complement."""
    nc = int(M_CC.shape[0])
    if nc == 0:
        return {
            "n": 0,
            "max_abs_row_sum": 0.0,
            "l2_row_sum": 0.0,
            "mean_row_sum": 0.0,
        }
    one = np.ones(nc, dtype=np.float64)
    rhs = M_GC @ one
    sol = cho_solve(M_GG_chol, rhs)
    row_sum = M_CC @ one - M_GC.T @ sol
    return {
        "n": nc,
        "max_abs_row_sum": float(np.max(np.abs(row_sum))),
        "l2_row_sum": float(np.linalg.norm(row_sum)),
        "mean_row_sum": float(np.mean(row_sum)),
    }


def _component_stats(adjacency_mask: np.ndarray) -> tuple[int, int]:
    """Connected-component count and largest-component size for a symmetric mask."""
    n = int(adjacency_mask.shape[0])
    if n == 0:
        return 0, 0
    if n == 1:
        return 1, 1
    adjacency = csr_matrix(adjacency_mask)
    n_components, labels = connected_components(adjacency, directed=False, connection="weak")
    largest = int(np.bincount(labels, minlength=n_components).max()) if n_components > 0 else 0
    return int(n_components), largest


def _effective_laplacian_sign_diagnostics(
    S_C: np.ndarray,
    row_sum_diag: dict[str, Any] | None,
    tol: float = 1.0e-10,
) -> dict[str, Any]:
    """Dense diagnostics for the ordinary-Laplacian shortcut versus signed-PSD route."""
    sym = np.asarray(0.5 * (S_C + S_C.T), dtype=np.float64)
    n = int(sym.shape[0])
    if n == 0:
        return {
            "audit_requested": True,
            "dense_audit_available": True,
            "max_row_sum_residual": 0.0,
            "num_positive_offdiag": 0,
            "num_negative_offdiag": 0,
            "max_positive_offdiag": 0.0,
            "min_negative_offdiag": 0.0,
            "effective_weight_min": 0.0,
            "effective_support_num_edges": 0,
            "effective_support_components": 0,
            "effective_support_largest_component": 0,
            "negative_edge_support_num_edges": 0,
            "negative_edge_support_components": 0,
            "negative_edge_support_largest_component": 0,
            "algebraic_connectivity_on_C": None,
            "ordinary_laplacian_candidate": True,
            "ordinary_laplacian_connected": False,
            "route_verdict": "ordinary_laplacian_confirmed",
        }

    offdiag_mask = ~np.eye(n, dtype=bool)
    offdiag_vals = sym[offdiag_mask]
    positive_mask = offdiag_vals > tol
    negative_mask = offdiag_vals < -tol
    num_positive = int(np.sum(positive_mask))
    num_negative = int(np.sum(negative_mask))
    max_positive = float(np.max(offdiag_vals[positive_mask])) if num_positive else 0.0
    min_negative = float(np.min(offdiag_vals[negative_mask])) if num_negative else 0.0
    effective_weight_min = float(np.min(-offdiag_vals)) if offdiag_vals.size else 0.0

    abs_support = np.abs(sym) > tol
    np.fill_diagonal(abs_support, False)
    eff_components, eff_largest = _component_stats(abs_support)

    negative_support = sym < -tol
    np.fill_diagonal(negative_support, False)
    neg_components, neg_largest = _component_stats(negative_support)

    effective_support_num_edges = int(np.count_nonzero(np.triu(abs_support, k=1)))
    negative_edge_support_num_edges = int(np.count_nonzero(np.triu(negative_support, k=1)))

    evals = _sym_eigvals(sym)
    algebraic_connectivity = float(evals[1]) if n >= 2 else None
    max_row_sum_residual = float((row_sum_diag or {}).get("max_abs_row_sum", float("nan")))
    ordinary_candidate = bool(num_positive == 0 and max_row_sum_residual <= tol)
    ordinary_connected = bool(ordinary_candidate and neg_components == 1)
    if ordinary_connected:
        route_verdict = "ordinary_laplacian_confirmed"
    else:
        route_verdict = "signed_psd_required"

    return {
        "audit_requested": True,
        "dense_audit_available": True,
        "max_row_sum_residual": max_row_sum_residual,
        "num_positive_offdiag": num_positive,
        "num_negative_offdiag": num_negative,
        "max_positive_offdiag": max_positive,
        "min_negative_offdiag": min_negative,
        "effective_weight_min": effective_weight_min,
        "effective_support_num_edges": effective_support_num_edges,
        "effective_support_components": eff_components,
        "effective_support_largest_component": eff_largest,
        "negative_edge_support_num_edges": negative_edge_support_num_edges,
        "negative_edge_support_components": neg_components,
        "negative_edge_support_largest_component": neg_largest,
        "algebraic_connectivity_on_C": algebraic_connectivity,
        "ordinary_laplacian_candidate": ordinary_candidate,
        "ordinary_laplacian_connected": ordinary_connected,
        "route_verdict": route_verdict,
    }


def _laplacian_from_weights(weights: np.ndarray) -> np.ndarray:
    """Build a Laplacian from a symmetric nonnegative weight matrix."""
    sym = np.asarray(0.5 * (weights + weights.T), dtype=np.float64)
    np.fill_diagonal(sym, 0.0)
    diag = np.sum(sym, axis=1)
    return np.diag(diag) - sym


def _reduced_one_perp(sym: np.ndarray) -> np.ndarray:
    """Restrict a symmetric matrix to 1^⊥ using an orthonormal basis."""
    n = int(sym.shape[0])
    if n <= 1:
        return np.zeros((0, 0), dtype=np.float64)
    one = np.ones((n, 1), dtype=np.float64)
    q_one = one / np.linalg.norm(one)
    projector = np.eye(n, dtype=np.float64) - q_one @ q_one.T
    q, _ = np.linalg.qr(projector)
    basis = q[:, : n - 1]
    return basis.T @ sym @ basis


def _one_perp_basis(n: int) -> np.ndarray:
    """Orthonormal basis for 1^⊥ in R^n."""
    if n <= 1:
        return np.zeros((n, 0), dtype=np.float64)
    one = np.ones((n, 1), dtype=np.float64)
    q_one = one / np.linalg.norm(one)
    projector = np.eye(n, dtype=np.float64) - q_one @ q_one.T
    q, _ = np.linalg.qr(projector)
    return q[:, : n - 1]


def _signed_factorization_diagnostics(
    S_C: np.ndarray,
    tol: float = 1.0e-10,
) -> dict[str, Any]:
    """Dense diagnostics for the live signed-PSD Schur route S_C = L_good - L_bad."""
    sym = np.asarray(0.5 * (S_C + S_C.T), dtype=np.float64)
    n = int(sym.shape[0])
    if n <= 1:
        return {
            "audit_requested": True,
            "dense_audit_available": True,
            "decomposition": "S_C = L_good - L_bad",
            "L_good_trace": 0.0,
            "L_bad_trace": 0.0,
            "L_good_nullity_estimate": 0,
            "L_bad_nullity_estimate": 0,
            "L_good_lambda1": None,
            "L_bad_lambda_max": None,
            "good_minus_bad_lambda_min_one_perp": None,
            "domination_ratio_sup_one_perp": None,
            "domination_holds_strictly_observed": None,
            "good_bad_commutator_fro": 0.0,
        }

    offdiag_good = np.maximum(-sym, 0.0)
    offdiag_bad = np.maximum(sym, 0.0)
    np.fill_diagonal(offdiag_good, 0.0)
    np.fill_diagonal(offdiag_bad, 0.0)

    L_good = _laplacian_from_weights(offdiag_good)
    L_bad = _laplacian_from_weights(offdiag_bad)

    evals_good = _sym_eigvals(L_good)
    evals_bad = _sym_eigvals(L_bad)
    reduced_good = _reduced_one_perp(L_good)
    reduced_bad = _reduced_one_perp(L_bad)
    reduced_sc = _reduced_one_perp(sym)

    domination_ratio = None
    domination_holds = None
    if reduced_good.size:
        min_good = float(np.min(_sym_eigvals(reduced_good)))
        if min_good > tol:
            eigvals_dom = eigh(reduced_bad, reduced_good, eigvals_only=True, driver="gvd")
            domination_ratio = float(np.max(eigvals_dom)) if eigvals_dom.size else 0.0
            domination_holds = bool(domination_ratio < 1.0 + 1.0e-8)

    commutator = L_good @ L_bad - L_bad @ L_good

    return {
        "audit_requested": True,
        "dense_audit_available": True,
        "decomposition": "S_C = L_good - L_bad",
        "L_good_trace": float(np.trace(L_good)),
        "L_bad_trace": float(np.trace(L_bad)),
        "L_good_nullity_estimate": int(np.sum(np.abs(evals_good) <= 1.0e-10)),
        "L_bad_nullity_estimate": int(np.sum(np.abs(evals_bad) <= 1.0e-10)),
        "L_good_lambda1": float(evals_good[1]) if n >= 2 else None,
        "L_bad_lambda_max": float(evals_bad[-1]) if evals_bad.size else None,
        "good_minus_bad_lambda_min_one_perp": (
            float(np.min(_sym_eigvals(reduced_sc))) if reduced_sc.size else None
        ),
        "domination_ratio_sup_one_perp": domination_ratio,
        "domination_holds_strictly_observed": domination_holds,
        "good_bad_commutator_fro": float(np.linalg.norm(commutator, ord="fro")),
    }


def _shell_pair_label(shell_i: int, shell_j: int) -> str:
    lo, hi = sorted((int(shell_i), int(shell_j)))
    return f"{lo}<->{hi}"


def _is_axis_mode(key: tuple[int, int, int]) -> bool:
    return sum(int(v == 0) for v in key) >= 2


def _sign_pattern(key: tuple[int, int, int]) -> str:
    def _sgn(v: int) -> str:
        if v > 0:
            return "+"
        if v < 0:
            return "-"
        return "0"
    return "".join(_sgn(int(v)) for v in key)


def _zero_coordinate_class(key: tuple[int, int, int]) -> str:
    return f"{sum(int(v == 0) for v in key)}-zero"


def _sign_flip_parity(key: tuple[int, int, int]) -> str:
    negative_count = sum(int(v < 0) for v in key)
    return "odd-neg" if (negative_count % 2) else "even-neg"


def _coord_permutation_orbit(key: tuple[int, int, int]) -> str:
    orbit = tuple(sorted(abs(int(v)) for v in key))
    return "(" + ",".join(str(v) for v in orbit) + ")"


def _canonical_helical_vectors_for_mode(key: tuple[int, int, int]) -> tuple[np.ndarray, np.ndarray]:
    """Canonical Waleffe-style helical polarization pair for one nonzero mode.

    This is a candidate representation lens only. The current DASHI operator acts
    on scalar seam amplitudes, not on an authoritative helical state space.
    """
    kvec = np.asarray([float(int(v)) for v in key], dtype=np.float64)
    knorm = float(np.linalg.norm(kvec))
    if knorm <= 1.0e-14:
        raise ValueError(f"zero wavevector has no helical basis: {key}")
    khat = kvec / knorm
    refs = (
        np.asarray([0.0, 0.0, 1.0], dtype=np.float64),
        np.asarray([0.0, 1.0, 0.0], dtype=np.float64),
        np.asarray([1.0, 0.0, 0.0], dtype=np.float64),
    )
    e1 = None
    for ref in refs:
        trial = np.cross(ref, khat)
        tnorm = float(np.linalg.norm(trial))
        if tnorm > 1.0e-12:
            e1 = trial / tnorm
            break
    if e1 is None:
        raise ValueError(f"failed to construct transverse basis for mode {key}")
    e2 = np.cross(khat, e1)
    e2 /= max(float(np.linalg.norm(e2)), 1.0e-300)
    h_plus = (e1 + 1.0j * e2) / math.sqrt(2.0)
    h_minus = (e1 - 1.0j * e2) / math.sqrt(2.0)
    return np.asarray(h_plus, dtype=np.complex128), np.asarray(h_minus, dtype=np.complex128)


def _canonical_helical_frames(
    mode_keys: list[tuple[int, int, int]],
) -> tuple[np.ndarray, np.ndarray]:
    plus = np.zeros((len(mode_keys), 3), dtype=np.complex128)
    minus = np.zeros((len(mode_keys), 3), dtype=np.complex128)
    for idx, key in enumerate(mode_keys):
        hp, hm = _canonical_helical_vectors_for_mode(key)
        plus[idx, :] = hp
        minus[idx, :] = hm
    return plus, minus


def _candidate_orbit_labels(n: int) -> list[str]:
    labels = [f"(0,1,{int(n - 1)})"]
    if n >= 7:
        labels.append(f"(1,7,{int(n)})")
    if n >= 5:
        labels.append(f"(1,{int(n - 5)},{int(n)})")
    out: list[str] = []
    seen: set[str] = set()
    for label in labels:
        if label not in seen:
            out.append(label)
            seen.add(label)
    return out


def _coarse_quotient_class_label(
    *,
    shell: int,
    key: tuple[int, int, int],
    scheme: str,
) -> str:
    orbit = _coord_permutation_orbit(key)
    zero_class = _zero_coordinate_class(key)
    parity = _sign_flip_parity(key)
    if scheme == "shell-orbit":
        return f"shell-{int(shell)}|orbit-{orbit}"
    if scheme == "shell-zero-orbit":
        return f"shell-{int(shell)}|{zero_class}|orbit-{orbit}"
    if scheme == "shell-zero-orbit-parity":
        return f"shell-{int(shell)}|{zero_class}|{parity}|orbit-{orbit}"
    if scheme == "shell-zero":
        return f"shell-{int(shell)}|{zero_class}"
    raise ValueError(f"unknown coarse quotient scheme: {scheme}")


def _dense_signed_laplacians(total: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    total_sym = np.asarray(0.5 * (total + total.T), dtype=np.float64)
    offdiag_good = np.maximum(-total_sym, 0.0)
    offdiag_bad = np.maximum(total_sym, 0.0)
    np.fill_diagonal(offdiag_good, 0.0)
    np.fill_diagonal(offdiag_bad, 0.0)
    return _laplacian_from_weights(offdiag_good), _laplacian_from_weights(offdiag_bad)


def _orthonormal_indicator_basis(labels: list[str]) -> tuple[np.ndarray, list[str], np.ndarray]:
    if not labels:
        return np.zeros((0, 0), dtype=np.float64), [], np.zeros(0, dtype=np.int64)
    unique_labels = sorted(set(labels))
    label_to_col = {label: idx for idx, label in enumerate(unique_labels)}
    q = np.zeros((len(labels), len(unique_labels)), dtype=np.float64)
    counts = np.zeros(len(unique_labels), dtype=np.int64)
    for row, label in enumerate(labels):
        col = label_to_col[label]
        q[row, col] = 1.0
        counts[col] += 1
    for col, count in enumerate(counts):
        q[:, col] /= math.sqrt(float(count))
    return q, unique_labels, counts


def _orth_basis_complement(vec: np.ndarray) -> np.ndarray:
    values = np.asarray(vec, dtype=np.float64).reshape(-1)
    n = int(values.shape[0])
    if n <= 1:
        return np.zeros((n, 0), dtype=np.float64)
    unit = values / max(float(np.linalg.norm(values)), 1.0e-300)
    projector = np.eye(n, dtype=np.float64) - np.outer(unit, unit)
    q, _ = np.linalg.qr(projector)
    return np.asarray(q[:, : n - 1], dtype=np.float64)


def _restricted_sector_mask(
    *,
    n: int,
    mode_keys: list[tuple[int, int, int]],
    include_nonaxis_only: bool = True,
    orbit_labels: list[str] | None = None,
) -> tuple[np.ndarray, dict[str, Any]]:
    labels = orbit_labels if orbit_labels is not None else _candidate_orbit_labels(n)
    label_set = set(labels)
    orbit_per_mode = [_coord_permutation_orbit(key) for key in mode_keys]
    axis_mask = np.asarray([_is_axis_mode(key) for key in mode_keys], dtype=bool)
    mask = np.asarray([orbit in label_set for orbit in orbit_per_mode], dtype=bool)
    if include_nonaxis_only:
        mask &= ~axis_mask
    return mask, {
        "orbit_labels": labels,
        "nonaxis_only": bool(include_nonaxis_only),
        "selected_mode_count": int(np.sum(mask)),
        "selected_orbit_mass_labels": sorted(label_set),
    }


def _schur_support_adjacency(
    total: np.ndarray,
    *,
    support_tol: float,
    allowed_mask: np.ndarray | None = None,
) -> np.ndarray:
    support = np.abs(np.asarray(total, dtype=np.float64)) > float(support_tol)
    support = np.asarray(support, dtype=bool)
    np.fill_diagonal(support, False)
    if allowed_mask is not None:
        allowed = np.asarray(allowed_mask, dtype=bool)
        support &= allowed[:, None]
        support &= allowed[None, :]
    return support


def _expand_halo_radius(
    adjacency: np.ndarray,
    seed_mask: np.ndarray,
    *,
    max_radius: int,
) -> list[np.ndarray]:
    support = np.asarray(adjacency, dtype=bool)
    seed = np.asarray(seed_mask, dtype=bool)
    if support.shape[0] != support.shape[1]:
        raise ValueError("adjacency must be square")
    if seed.shape[0] != support.shape[0]:
        raise ValueError("seed mask must match adjacency dimension")
    masks: list[np.ndarray] = []
    current = seed.copy()
    frontier = seed.copy()
    masks.append(current.copy())
    for _radius in range(1, max_radius + 1):
        if np.any(frontier):
            grown = np.any(support[frontier, :], axis=0)
        else:
            grown = np.zeros_like(current)
        frontier = grown & ~current
        if not np.any(frontier):
            masks.append(current.copy())
            continue
        current = current | frontier
        masks.append(current.copy())
    return masks


def _build_chunked_signed_laplacian_state(
    M_CC: np.ndarray,
    correction: np.ndarray,
    *,
    row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
) -> dict[str, Any]:
    n = int(M_CC.shape[0])
    degree_good = np.zeros(n, dtype=np.float64)
    degree_bad = np.zeros(n, dtype=np.float64)
    sign_stats = {
        "num_positive_offdiag": 0,
        "num_negative_offdiag": 0,
        "max_positive_offdiag": 0.0,
        "min_negative_offdiag": 0.0,
    }
    for start in range(0, n, row_chunk):
        stop = min(start + row_chunk, n)
        total_chunk = np.asarray(M_CC[start:stop, :] - correction[start:stop, :], dtype=np.float64)
        diag_rows = np.arange(stop - start, dtype=np.int64)
        diag_cols = np.arange(start, stop, dtype=np.int64) - start

        offdiag_vals = total_chunk.copy()
        offdiag_vals[diag_rows, diag_cols] = 0.0
        positive_mask = offdiag_vals > 1.0e-10
        negative_mask = offdiag_vals < -1.0e-10
        sign_stats["num_positive_offdiag"] += int(np.sum(positive_mask))
        sign_stats["num_negative_offdiag"] += int(np.sum(negative_mask))
        if np.any(positive_mask):
            sign_stats["max_positive_offdiag"] = max(
                float(sign_stats["max_positive_offdiag"]),
                float(np.max(offdiag_vals[positive_mask])),
            )
        if np.any(negative_mask):
            min_negative = float(np.min(offdiag_vals[negative_mask]))
            if sign_stats["min_negative_offdiag"] == 0.0:
                sign_stats["min_negative_offdiag"] = min_negative
            else:
                sign_stats["min_negative_offdiag"] = min(
                    float(sign_stats["min_negative_offdiag"]),
                    min_negative,
                )

        good_weights = np.maximum(-total_chunk, 0.0)
        bad_weights = np.maximum(total_chunk, 0.0)
        good_weights[diag_rows, diag_cols] = 0.0
        bad_weights[diag_rows, diag_cols] = 0.0
        degree_good[start:stop] = np.sum(good_weights, axis=1)
        degree_bad[start:stop] = np.sum(bad_weights, axis=1)

    return {
        "degree_good": degree_good,
        "degree_bad": degree_bad,
        "row_chunk": int(row_chunk),
        "sign_stats": sign_stats,
    }


def _signed_laplacian_apply(
    x: np.ndarray,
    *,
    M_CC: np.ndarray,
    correction: np.ndarray,
    state: _ChunkedSignedLaplacian,
) -> np.ndarray:
    values = np.asarray(x, dtype=np.float64)
    if values.ndim == 1:
        vec = _project_mean_zero(values)
        n = int(len(vec))
        out = np.zeros(n, dtype=np.float64)
        for start in range(0, n, state.row_chunk):
            stop = min(start + state.row_chunk, n)
            total_chunk = np.asarray(M_CC[start:stop, :] - correction[start:stop, :], dtype=np.float64)
            weights = (
                np.maximum(-total_chunk, 0.0)
                if state.kind == "good"
                else np.maximum(total_chunk, 0.0)
            )
            diag_rows = np.arange(stop - start, dtype=np.int64)
            diag_cols = np.arange(start, stop, dtype=np.int64) - start
            weights[diag_rows, diag_cols] = 0.0
            out[start:stop] = state.degree[start:stop] * vec[start:stop] - weights @ vec
        return _project_mean_zero(out)

    if values.ndim == 2:
        centered = values - np.mean(values, axis=0, keepdims=True)
        n, ncols = centered.shape
        out = np.zeros((n, ncols), dtype=np.float64)
        for start in range(0, n, state.row_chunk):
            stop = min(start + state.row_chunk, n)
            total_chunk = np.asarray(M_CC[start:stop, :] - correction[start:stop, :], dtype=np.float64)
            weights = (
                np.maximum(-total_chunk, 0.0)
                if state.kind == "good"
                else np.maximum(total_chunk, 0.0)
            )
            diag_rows = np.arange(stop - start, dtype=np.int64)
            diag_cols = np.arange(start, stop, dtype=np.int64) - start
            weights[diag_rows, diag_cols] = 0.0
            out[start:stop, :] = state.degree[start:stop, None] * centered[start:stop, :] - weights @ centered
        return out - np.mean(out, axis=0, keepdims=True)

    raise ValueError(f"expected vector or matrix input, got ndim={values.ndim}")


def _torch_gpu_available() -> bool:
    if importlib.util.find_spec("torch") is None:
        return False
    try:
        import torch  # type: ignore
    except Exception:
        return False
    cuda_ok = bool(getattr(torch, "cuda", None) is not None and torch.cuda.is_available())
    hip_ok = bool(getattr(torch.version, "hip", None))
    return bool(cuda_ok or hip_ok)


def _make_restricted_backend(
    *,
    M_CC: np.ndarray,
    correction: np.ndarray,
    row_chunk: int,
    backend: str,
    gpu_checks: int,
) -> _RestrictedBackend:
    setup = _build_chunked_signed_laplacian_state(M_CC, correction, row_chunk=row_chunk)
    good_state = _ChunkedSignedLaplacian("good", np.asarray(setup["degree_good"], dtype=np.float64), int(row_chunk))
    bad_state = _ChunkedSignedLaplacian("bad", np.asarray(setup["degree_bad"], dtype=np.float64), int(row_chunk))

    def cpu_good_mv(x: np.ndarray) -> np.ndarray:
        return _signed_laplacian_apply(x, M_CC=M_CC, correction=correction, state=good_state)

    def cpu_bad_mv(x: np.ndarray) -> np.ndarray:
        return _signed_laplacian_apply(x, M_CC=M_CC, correction=correction, state=bad_state)

    if backend == "cpu":
        return _RestrictedBackend(
            name="cpu",
            good_mv=cpu_good_mv,
            bad_mv=cpu_bad_mv,
            info={
                "gpu_domination_scout_installed": False,
                "gpu_domination_scout_matches_cpu": None,
                "gpu_kn_authority": False,
                "gpu_available": False,
                "gpu_backend_status": "not_requested",
            },
        )

    if backend == "vulkan-scout":
        if create_vulkan_triad_laplacian_executor is None or not has_vulkan_triad_laplacian():
            return _RestrictedBackend(
                name="cpu-fallback",
                good_mv=cpu_good_mv,
                bad_mv=cpu_bad_mv,
                info={
                    "gpu_domination_scout_installed": True,
                    "gpu_domination_scout_matches_cpu": None,
                    "gpu_kn_authority": False,
                    "gpu_available": False,
                    "gpu_backend_status": "vulkan_triad_laplacian_unavailable",
                    "gpu_backend_name": "vulkan-scout",
                    "gpu_cpu_parity_observed": False,
                },
            )

        total = np.asarray(M_CC - correction, dtype=np.float64)
        weights_good = np.maximum(-total, 0.0)
        weights_bad = np.maximum(total, 0.0)
        np.fill_diagonal(weights_good, 0.0)
        np.fill_diagonal(weights_bad, 0.0)
        profile = profile_from_weight_matrices(
            weights_good,
            weights_bad,
            profile_id="schur-sign-split",
        )
        executor, probe_info = create_vulkan_triad_laplacian_executor(profile)

        def gpu_good_mv(x: np.ndarray) -> np.ndarray:
            return _project_mean_zero(executor.matvec_abs(np.asarray(x, dtype=np.float64)))

        def gpu_bad_mv(x: np.ndarray) -> np.ndarray:
            return _project_mean_zero(executor.matvec_neg(np.asarray(x, dtype=np.float64)))

        rng = np.random.default_rng(12345)
        good_errors: list[float] = []
        bad_errors: list[float] = []
        for _ in range(max(int(gpu_checks), 0)):
            probe = rng.standard_normal(M_CC.shape[0])
            probe /= max(float(np.linalg.norm(probe)), 1.0e-300)
            good_errors.append(float(np.max(np.abs(gpu_good_mv(probe) - cpu_good_mv(probe)))))
            bad_errors.append(float(np.max(np.abs(gpu_bad_mv(probe) - cpu_bad_mv(probe)))))
        max_good_error = max(good_errors) if good_errors else None
        max_bad_error = max(bad_errors) if bad_errors else None
        parity_ok = bool(
            max_good_error is not None
            and max_bad_error is not None
            and max_good_error <= 5.0e-5
            and max_bad_error <= 5.0e-5
        )
        if not parity_ok:
            executor.close()
            return _RestrictedBackend(
                name="cpu-fallback",
                good_mv=cpu_good_mv,
                bad_mv=cpu_bad_mv,
                info={
                    "gpu_domination_scout_installed": True,
                    "gpu_domination_scout_matches_cpu": False,
                    "gpu_kn_authority": False,
                    "gpu_available": True,
                    "gpu_backend_status": "parity_failed_cpu_fallback",
                    "gpu_backend_name": "vulkan-scout",
                    "gpu_vulkan_icd": probe_info.get("vulkan_icd"),
                    "gpu_icd_probe_errors": probe_info.get("icd_probe_errors", []),
                    "gpu_matvec_max_abs_error_good": max_good_error,
                    "gpu_matvec_max_abs_error_bad": max_bad_error,
                    "gpu_cpu_parity_observed": False,
                },
            )

        return _RestrictedBackend(
            name="vulkan-scout",
            good_mv=gpu_good_mv,
            bad_mv=gpu_bad_mv,
            close=executor.close,
            info={
                "gpu_domination_scout_installed": True,
                "gpu_domination_scout_matches_cpu": True,
                "gpu_kn_authority": False,
                "gpu_available": True,
                "gpu_backend_status": "ok",
                "gpu_backend_name": "vulkan-scout",
                "gpu_vulkan_icd": probe_info.get("vulkan_icd"),
                "gpu_icd_probe_errors": probe_info.get("icd_probe_errors", []),
                "gpu_matvec_max_abs_error_good": max_good_error,
                "gpu_matvec_max_abs_error_bad": max_bad_error,
                "gpu_cpu_parity_observed": True,
            },
        )

    if backend != "torch-gpu-scout":
        raise ValueError(f"unknown restricted backend: {backend}")

    if not _torch_gpu_available():
        return _RestrictedBackend(
            name="cpu-fallback",
            good_mv=cpu_good_mv,
            bad_mv=cpu_bad_mv,
            info={
                "gpu_domination_scout_installed": False,
                "gpu_domination_scout_matches_cpu": None,
                "gpu_kn_authority": False,
                "gpu_available": False,
                "gpu_backend_status": "torch_gpu_unavailable",
            },
        )

    import torch  # type: ignore

    device = "cuda" if torch.cuda.is_available() else "cpu"
    total = np.asarray(M_CC - correction, dtype=np.float32)
    weights_good = np.maximum(-total, 0.0)
    weights_bad = np.maximum(total, 0.0)
    np.fill_diagonal(weights_good, 0.0)
    np.fill_diagonal(weights_bad, 0.0)
    degree_good = np.sum(weights_good, axis=1, dtype=np.float64).astype(np.float32)
    degree_bad = np.sum(weights_bad, axis=1, dtype=np.float64).astype(np.float32)
    tg_good = torch.as_tensor(weights_good, dtype=torch.float32, device=device)
    tg_bad = torch.as_tensor(weights_bad, dtype=torch.float32, device=device)
    td_good = torch.as_tensor(degree_good, dtype=torch.float32, device=device)
    td_bad = torch.as_tensor(degree_bad, dtype=torch.float32, device=device)

    def _torch_apply(values: np.ndarray, *, weights: Any, degree: Any) -> np.ndarray:
        arr = np.asarray(values, dtype=np.float64)
        if arr.ndim == 1:
            centered = _project_mean_zero(arr).astype(np.float32, copy=False)
            tv = torch.as_tensor(centered, dtype=torch.float32, device=device)
            out = degree * tv - weights @ tv
            result = out.detach().cpu().numpy().astype(np.float64, copy=False)
            return _project_mean_zero(result)
        if arr.ndim == 2:
            centered = arr - np.mean(arr, axis=0, keepdims=True)
            tv = torch.as_tensor(centered.astype(np.float32, copy=False), dtype=torch.float32, device=device)
            out = degree[:, None] * tv - weights @ tv
            result = out.detach().cpu().numpy().astype(np.float64, copy=False)
            return result - np.mean(result, axis=0, keepdims=True)
        raise ValueError(f"expected vector or matrix input, got ndim={arr.ndim}")

    def gpu_good_mv(x: np.ndarray) -> np.ndarray:
        return _torch_apply(x, weights=tg_good, degree=td_good)

    def gpu_bad_mv(x: np.ndarray) -> np.ndarray:
        return _torch_apply(x, weights=tg_bad, degree=td_bad)

    rng = np.random.default_rng(12345)
    good_errors: list[float] = []
    bad_errors: list[float] = []
    for _ in range(max(int(gpu_checks), 0)):
        probe = rng.standard_normal(M_CC.shape[0])
        probe /= max(float(np.linalg.norm(probe)), 1.0e-300)
        good_errors.append(float(np.max(np.abs(gpu_good_mv(probe) - cpu_good_mv(probe)))))
        bad_errors.append(float(np.max(np.abs(gpu_bad_mv(probe) - cpu_bad_mv(probe)))))
    max_good_error = max(good_errors) if good_errors else None
    max_bad_error = max(bad_errors) if bad_errors else None
    parity_ok = bool(
        max_good_error is not None
        and max_bad_error is not None
        and max_good_error <= 5.0e-5
        and max_bad_error <= 5.0e-5
    )
    if not parity_ok:
        return _RestrictedBackend(
            name="cpu-fallback",
            good_mv=cpu_good_mv,
            bad_mv=cpu_bad_mv,
            info={
                "gpu_domination_scout_installed": True,
                "gpu_domination_scout_matches_cpu": False,
                "gpu_kn_authority": False,
                "gpu_available": True,
                "gpu_backend_status": "parity_failed_cpu_fallback",
                "gpu_backend_name": "torch-gpu-scout",
                "gpu_matvec_max_abs_error_good": max_good_error,
                "gpu_matvec_max_abs_error_bad": max_bad_error,
                "gpu_cpu_parity_observed": False,
            },
        )

    return _RestrictedBackend(
        name="torch-gpu-scout",
        good_mv=gpu_good_mv,
        bad_mv=gpu_bad_mv,
        info={
            "gpu_domination_scout_installed": True,
            "gpu_domination_scout_matches_cpu": True,
            "gpu_kn_authority": False,
            "gpu_available": True,
            "gpu_backend_status": "ok",
            "gpu_backend_name": "torch-gpu-scout",
            "gpu_device": device,
            "gpu_matvec_max_abs_error_good": max_good_error,
            "gpu_matvec_max_abs_error_bad": max_bad_error,
            "gpu_cpu_parity_observed": True,
        },
    )


def _solve_projected_extremal_mode(
    operator: LinearOperator,
    *,
    largest: bool,
    n: int,
    seed: int,
    constraints: np.ndarray | None = None,
    b_operator: LinearOperator | None = None,
    tol: float = 1.0e-8,
    maxiter: int = 120,
    center_guess: bool = False,
) -> tuple[float, np.ndarray, float]:
    rng = np.random.default_rng(int(seed))
    guess = rng.standard_normal((n, 1))
    if constraints is not None:
        for col in range(int(constraints.shape[1])):
            basis = np.asarray(constraints[:, col], dtype=np.float64)
            denom = float(basis @ basis)
            if denom > 0.0:
                guess -= basis[:, None] * ((basis @ guess[:, 0]) / denom)
    if center_guess:
        guess[:, 0] = _project_mean_zero(guess[:, 0])
    norm = float(np.linalg.norm(guess[:, 0]))
    if norm <= 1.0e-14:
        guess[:, 0] = np.linspace(-1.0, 1.0, n, dtype=np.float64)
        if center_guess:
            guess[:, 0] = _project_mean_zero(guess[:, 0])
        norm = float(np.linalg.norm(guess[:, 0]))
    guess[:, 0] /= max(norm, 1.0e-300)

    eigvals, eigvecs, residuals = lobpcg(
        operator,
        guess,
        B=b_operator,
        Y=constraints,
        tol=float(tol),
        maxiter=int(maxiter),
        largest=bool(largest),
        retResidualNormsHistory=True,
    )
    value = float(np.asarray(eigvals, dtype=np.float64)[0])
    vec = np.asarray(eigvecs[:, 0], dtype=np.float64)
    if center_guess:
        vec = _project_mean_zero(vec)
    vec /= max(float(np.linalg.norm(vec)), 1.0e-300)
    residual_history = np.asarray(residuals, dtype=np.float64).reshape(-1)
    residual_norm = float(residual_history[-1]) if residual_history.size else float("nan")
    return value, vec, residual_norm


def _vector_support_diagnostics(
    vec: np.ndarray,
    *,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    degree_good: np.ndarray,
    degree_bad: np.ndarray,
    top_k: int = 20,
) -> dict[str, Any]:
    values = np.asarray(vec, dtype=np.float64)
    norm = float(np.linalg.norm(values))
    if norm <= 1.0e-14:
        return {"error": "zero_vector"}
    unit = values / norm
    mass = unit * unit
    shell_mass = {
        str(shell): float(np.sum(mass[shell_levels == float(shell)]))
        for shell in sorted({int(v) for v in shell_levels})
    }
    axis_mask = np.asarray([_is_axis_mode(key) for key in mode_keys], dtype=bool)
    sign_mass: dict[str, float] = {}
    for idx, key in enumerate(mode_keys):
        label = _sign_pattern(key)
        sign_mass[label] = sign_mass.get(label, 0.0) + float(mass[idx])
    abs_order = np.argsort(-np.abs(unit))
    top_modes = [
        {
            "rank": int(rank + 1),
            "mode": [int(v) for v in mode_keys[int(index)]],
            "shell": int(shell_levels[int(index)]),
            "value": float(unit[int(index)]),
            "abs_value": float(abs(unit[int(index)])),
            "mass": float(mass[int(index)]),
            "is_axis": bool(axis_mask[int(index)]),
        }
        for rank, index in enumerate(abs_order[:top_k])
    ]
    one = np.ones(len(unit), dtype=np.float64)
    shell_values = np.asarray(shell_levels, dtype=np.float64)
    degree_total = np.asarray(degree_good + degree_bad, dtype=np.float64)

    def _corr(reference: np.ndarray) -> float | None:
        ref = np.asarray(reference, dtype=np.float64)
        denom = float(np.linalg.norm(ref) * np.linalg.norm(unit))
        if denom <= 1.0e-14:
            return None
        return float(unit @ ref / denom)

    return {
        "shell_mass": shell_mass,
        "constant_correlation": _corr(one),
        "degree_correlation": _corr(degree_total),
        "sqrt_degree_correlation": _corr(np.sqrt(np.clip(degree_total, 0.0, None))),
        "shell_value_correlation": _corr(shell_values),
        "axis_concentration": float(np.sum(mass[axis_mask])) if axis_mask.size else 0.0,
        "nonaxis_concentration": float(np.sum(mass[~axis_mask])) if axis_mask.size else 0.0,
        "sign_pattern_mass": {key: float(value) for key, value in sorted(sign_mass.items())},
        "top_modes": top_modes,
    }


def _restricted_rayleigh_ratio(
    vec: np.ndarray,
    *,
    mask: np.ndarray,
    M_CC: np.ndarray,
    correction: np.ndarray,
    good_state: _ChunkedSignedLaplacian,
    bad_state: _ChunkedSignedLaplacian,
) -> dict[str, Any]:
    unit = np.asarray(vec, dtype=np.float64)
    unit /= max(float(np.linalg.norm(unit)), 1.0e-300)
    mask_arr = np.asarray(mask, dtype=bool)
    component = np.where(mask_arr, unit, 0.0)
    component = _project_mean_zero(component)
    norm = float(np.linalg.norm(component))
    if norm <= 1.0e-14:
        return {"mass": 0.0, "good_energy": 0.0, "bad_energy": 0.0, "ratio": None}
    component /= norm
    good_energy = float(
        component @ _signed_laplacian_apply(component, M_CC=M_CC, correction=correction, state=good_state)
    )
    bad_energy = float(
        component @ _signed_laplacian_apply(component, M_CC=M_CC, correction=correction, state=bad_state)
    )
    return {
        "mass": float(np.sum(unit[mask_arr] ** 2)),
        "good_energy": good_energy,
        "bad_energy": bad_energy,
        "ratio": float(bad_energy / good_energy) if good_energy > 1.0e-14 else None,
    }


def _symmetry_sector_diagnostics(
    vec: np.ndarray,
    *,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    M_CC: np.ndarray,
    correction: np.ndarray,
    good_state: _ChunkedSignedLaplacian,
    bad_state: _ChunkedSignedLaplacian,
    top_k: int = 12,
) -> dict[str, Any]:
    values = np.asarray(vec, dtype=np.float64)
    norm = float(np.linalg.norm(values))
    if norm <= 1.0e-14:
        return {"error": "zero_vector"}
    unit = values / norm
    mass = unit * unit
    axis_mask = np.asarray([_is_axis_mode(key) for key in mode_keys], dtype=bool)
    orbit_labels = [_coord_permutation_orbit(key) for key in mode_keys]
    zero_labels = [_zero_coordinate_class(key) for key in mode_keys]
    parity_labels = [_sign_flip_parity(key) for key in mode_keys]
    shell_labels = [f"shell-{int(shell)}" for shell in shell_levels]
    axis_labels = ["axis" if axis_mask[idx] else "nonaxis" for idx in range(len(mode_keys))]

    def _mass_by_label(labels: list[str]) -> dict[str, float]:
        out: dict[str, float] = {}
        for idx, label in enumerate(labels):
            out[label] = out.get(label, 0.0) + float(mass[idx])
        return dict(sorted(out.items(), key=lambda item: (-item[1], item[0])))

    def _component_ratios(labels: list[str], mass_by_label: dict[str, float]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for label, _label_mass in list(mass_by_label.items())[:top_k]:
            out[label] = _restricted_rayleigh_ratio(
                unit,
                mask=np.asarray([entry == label for entry in labels], dtype=bool),
                M_CC=M_CC,
                correction=correction,
                good_state=good_state,
                bad_state=bad_state,
            )
        return out

    orbit_mass = _mass_by_label(orbit_labels)
    zero_mass = _mass_by_label(zero_labels)
    parity_mass = _mass_by_label(parity_labels)
    shell_mass = _mass_by_label(shell_labels)
    axis_mass = _mass_by_label(axis_labels)

    top_mode_sector_labels = []
    for rank, index in enumerate(np.argsort(-np.abs(unit))[:top_k]):
        idx = int(index)
        top_mode_sector_labels.append(
            {
                "rank": int(rank + 1),
                "mode": [int(v) for v in mode_keys[idx]],
                "orbit": orbit_labels[idx],
                "zero_class": zero_labels[idx],
                "sign_flip_parity": parity_labels[idx],
                "shell": int(shell_levels[idx]),
                "is_axis": bool(axis_mask[idx]),
                "mass": float(mass[idx]),
            }
        )

    return {
        "coordinate_permutation_orbit_mass": orbit_mass,
        "zero_coordinate_class_mass": zero_mass,
        "sign_flip_parity_mass": parity_mass,
        "shell_class_mass": shell_mass,
        "axis_class_mass": axis_mass,
        "coordinate_permutation_orbit_component_ratio": _component_ratios(orbit_labels, orbit_mass),
        "zero_coordinate_class_component_ratio": _component_ratios(zero_labels, zero_mass),
        "sign_flip_parity_component_ratio": _component_ratios(parity_labels, parity_mass),
        "shell_class_component_ratio": _component_ratios(shell_labels, shell_mass),
        "axis_class_component_ratio": _component_ratios(axis_labels, axis_mass),
        "top_mode_sector_labels": top_mode_sector_labels,
    }


def _extremizer_angular_frame_diagnostics(
    vec: np.ndarray,
    *,
    mode_keys: list[tuple[int, int, int]],
    top_k: int = 20,
    target_tol: float = 0.075,
) -> dict[str, Any]:
    values = np.asarray(vec, dtype=np.float64)
    norm = float(np.linalg.norm(values))
    if norm <= 1.0e-14:
        return {"error": "zero_vector"}
    unit = values / norm
    mass = unit * unit
    top_indices = np.argsort(-np.abs(unit))[: min(top_k, len(unit))]

    wavevectors: list[np.ndarray] = []
    weights: list[float] = []
    top_modes: list[dict[str, Any]] = []
    for rank, index in enumerate(top_indices):
        idx = int(index)
        key = tuple(int(v) for v in mode_keys[idx])
        kvec = np.asarray(key, dtype=np.float64)
        knorm = float(np.linalg.norm(kvec))
        if knorm <= 1.0e-14:
            continue
        wavevectors.append(kvec / knorm)
        weights.append(float(mass[idx]))
        top_modes.append(
            {
                "rank": int(rank + 1),
                "mode": [int(v) for v in key],
                "mass": float(mass[idx]),
                "value": float(unit[idx]),
                "abs_value": float(abs(unit[idx])),
                "orbit": _coord_permutation_orbit(key),
            }
        )

    if not wavevectors:
        return {"error": "no_nonzero_wavevectors"}

    V = np.asarray(wavevectors, dtype=np.float64)
    w = np.asarray(weights, dtype=np.float64)
    dots = V @ V.T
    frame_op = np.zeros((3, 3), dtype=np.float64)
    for idx in range(len(V)):
        frame_op += w[idx] * np.outer(V[idx], V[idx])
    frame_eigs = np.linalg.eigvalsh(frame_op)
    op_norm = float(np.max(frame_eigs))
    trace = float(np.trace(frame_op))

    pairwise: list[dict[str, Any]] = []
    target_mass = {"-1/2": 0.0, "0": 0.0, "+1/2": 0.0}
    histogram = {
        "[-1.00,-0.75)": 0.0,
        "[-0.75,-0.25)": 0.0,
        "[-0.25,0.25)": 0.0,
        "[0.25,0.75)": 0.0,
        "[0.75,1.00]": 0.0,
    }
    total_pair_mass = 0.0
    for i in range(len(V)):
        for j in range(i + 1, len(V)):
            dot = float(dots[i, j])
            pair_mass = float(w[i] * w[j])
            total_pair_mass += pair_mass
            pairwise.append(
                {
                    "left_rank": int(i + 1),
                    "right_rank": int(j + 1),
                    "left_mode": top_modes[i]["mode"],
                    "right_mode": top_modes[j]["mode"],
                    "dot": dot,
                    "pair_mass": pair_mass,
                }
            )
            if dot < -0.75:
                histogram["[-1.00,-0.75)"] += pair_mass
            elif dot < -0.25:
                histogram["[-0.75,-0.25)"] += pair_mass
            elif dot < 0.25:
                histogram["[-0.25,0.25)"] += pair_mass
            elif dot < 0.75:
                histogram["[0.25,0.75)"] += pair_mass
            else:
                histogram["[0.75,1.00]"] += pair_mass
            if abs(dot + 0.5) <= target_tol:
                target_mass["-1/2"] += pair_mass
            if abs(dot) <= target_tol:
                target_mass["0"] += pair_mass
            if abs(dot - 0.5) <= target_tol:
                target_mass["+1/2"] += pair_mass

    if total_pair_mass > 1.0e-14:
        histogram = {key: float(value / total_pair_mass) for key, value in histogram.items()}
        target_mass = {key: float(value / total_pair_mass) for key, value in target_mass.items()}

    pairwise.sort(key=lambda item: (-item["pair_mass"], abs(item["dot"] + 0.5)))
    return {
        "top_modes": top_modes,
        "pairwise_dot_histogram_mass": histogram,
        "pairwise_dot_target_mass": target_mass,
        "top_pairwise_dots": pairwise[: min(20, len(pairwise))],
        "frame_operator_eigenvalues": [float(v) for v in frame_eigs],
        "frame_trace": trace,
        "frame_operator_norm": op_norm,
        "frame_trace_over_operator_norm": float(trace / op_norm) if op_norm > 1.0e-14 else None,
        "top_mode_mass_total": float(np.sum(w)),
    }


def _rayleigh_source_breakdown(
    vec: np.ndarray,
    *,
    M_CC: np.ndarray,
    correction: np.ndarray,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    row_chunk: int,
) -> dict[str, Any]:
    unit = np.asarray(vec, dtype=np.float64)
    unit = _project_mean_zero(unit)
    unit /= max(float(np.linalg.norm(unit)), 1.0e-300)
    n = int(len(unit))
    shell_int = np.asarray(shell_levels, dtype=np.int64)
    axis_mask = np.asarray([_is_axis_mode(key) for key in mode_keys], dtype=bool)

    total_good = 0.0
    total_bad = 0.0
    direct_good = 0.0
    direct_bad = 0.0
    mediated_good = 0.0
    mediated_bad = 0.0
    shell_pair_good: dict[str, float] = {}
    shell_pair_bad: dict[str, float] = {}
    sector_good = {"axis_axis": 0.0, "axis_mixed": 0.0, "nonaxis_nonaxis": 0.0}
    sector_bad = {"axis_axis": 0.0, "axis_mixed": 0.0, "nonaxis_nonaxis": 0.0}

    for start in range(0, n, row_chunk):
        stop = min(start + row_chunk, n)
        rows = np.arange(start, stop, dtype=np.int64)
        diff2 = (unit[start:stop, None] - unit[None, :]) ** 2

        total_chunk = np.asarray(M_CC[start:stop, :] - correction[start:stop, :], dtype=np.float64)
        direct_chunk = np.asarray(M_CC[start:stop, :], dtype=np.float64)
        mediated_chunk = np.asarray(-correction[start:stop, :], dtype=np.float64)

        diag_rows = np.arange(stop - start, dtype=np.int64)
        diag_cols = rows - start
        for chunk in (total_chunk, direct_chunk, mediated_chunk):
            chunk[diag_rows, diag_cols] = 0.0

        total_good_w = np.maximum(-total_chunk, 0.0)
        total_bad_w = np.maximum(total_chunk, 0.0)
        direct_good_w = np.maximum(-direct_chunk, 0.0)
        direct_bad_w = np.maximum(direct_chunk, 0.0)
        mediated_good_w = np.maximum(-mediated_chunk, 0.0)
        mediated_bad_w = np.maximum(mediated_chunk, 0.0)

        total_good += 0.5 * float(np.sum(total_good_w * diff2))
        total_bad += 0.5 * float(np.sum(total_bad_w * diff2))
        direct_good += 0.5 * float(np.sum(direct_good_w * diff2))
        direct_bad += 0.5 * float(np.sum(direct_bad_w * diff2))
        mediated_good += 0.5 * float(np.sum(mediated_good_w * diff2))
        mediated_bad += 0.5 * float(np.sum(mediated_bad_w * diff2))

        row_shells = shell_int[start:stop]
        for shell_a in sorted({int(v) for v in row_shells}):
            mask_a = row_shells == shell_a
            for shell_b in sorted({int(v) for v in shell_int}):
                label = _shell_pair_label(shell_a, shell_b)
                pair_mask = mask_a[:, None] & (shell_int[None, :] == shell_b)
                shell_pair_good[label] = shell_pair_good.get(label, 0.0) + 0.5 * float(
                    np.sum(total_good_w * diff2 * pair_mask)
                )
                shell_pair_bad[label] = shell_pair_bad.get(label, 0.0) + 0.5 * float(
                    np.sum(total_bad_w * diff2 * pair_mask)
                )

        row_axis = axis_mask[start:stop]
        aa = row_axis[:, None] & axis_mask[None, :]
        nn = (~row_axis)[:, None] & (~axis_mask[None, :])
        am = ~(aa | nn)
        for label, mask in (("axis_axis", aa), ("axis_mixed", am), ("nonaxis_nonaxis", nn)):
            sector_good[label] += 0.5 * float(np.sum(total_good_w * diff2 * mask))
            sector_bad[label] += 0.5 * float(np.sum(total_bad_w * diff2 * mask))

    total_ratio = float(total_bad / total_good) if total_good > 1.0e-14 else None
    shell_pair_ratio = {
        key: (
            float(shell_pair_bad[key] / shell_pair_good[key])
            if shell_pair_good.get(key, 0.0) > 1.0e-14
            else None
        )
        for key in sorted(set(shell_pair_good) | set(shell_pair_bad))
    }
    sector_ratio = {
        key: (float(sector_bad[key] / sector_good[key]) if sector_good[key] > 1.0e-14 else None)
        for key in sector_good
    }
    return {
        "rayleigh_ratio_on_extremizer": total_ratio,
        "direct": {
            "good_energy": float(direct_good),
            "bad_energy": float(direct_bad),
            "ratio": float(direct_bad / direct_good) if direct_good > 1.0e-14 else None,
        },
        "mediated": {
            "good_energy": float(mediated_good),
            "bad_energy": float(mediated_bad),
            "ratio": float(mediated_bad / mediated_good) if mediated_good > 1.0e-14 else None,
        },
        "shell_pair": {
            key: {
                "good_energy": float(shell_pair_good.get(key, 0.0)),
                "bad_energy": float(shell_pair_bad.get(key, 0.0)),
                "ratio": shell_pair_ratio.get(key),
            }
            for key in sorted(shell_pair_ratio)
        },
        "axis_sector": {
            key: {
                "good_energy": float(sector_good[key]),
                "bad_energy": float(sector_bad[key]),
                "ratio": sector_ratio[key],
            }
            for key in sector_good
        },
    }


def _domination_ratio_matrix_free_diagnostics(
    M_CC: np.ndarray,
    correction: np.ndarray,
    *,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    eps: float = DEFAULT_DOMINATION_EPS,
    tol: float = 1.0e-8,
    maxiter: int = 200,
    audit_symmetry_sectors: bool = False,
    audit_angular_frame: bool = False,
) -> dict[str, Any]:
    n = int(M_CC.shape[0])
    if n <= 1:
        return {
            "audit_requested": True,
            "dense_audit_available": False,
            "matrix_free_requested": True,
            "status": "trivial",
        }

    setup = _build_chunked_signed_laplacian_state(M_CC, correction, row_chunk=row_chunk)
    good_state = _ChunkedSignedLaplacian("good", np.asarray(setup["degree_good"], dtype=np.float64), int(row_chunk))
    bad_state = _ChunkedSignedLaplacian("bad", np.asarray(setup["degree_bad"], dtype=np.float64), int(row_chunk))
    reduced_n = n - 1

    def _good_mv(x: np.ndarray) -> np.ndarray:
        return _signed_laplacian_apply(x, M_CC=M_CC, correction=correction, state=good_state)

    def _bad_mv(x: np.ndarray) -> np.ndarray:
        return _signed_laplacian_apply(x, M_CC=M_CC, correction=correction, state=bad_state)

    def _good_eps_mv(x: np.ndarray) -> np.ndarray:
        vec = _project_mean_zero(np.asarray(x, dtype=np.float64))
        return _good_mv(vec) + float(eps) * vec

    def _reduced_from_full(full_mv):
        def apply(y: np.ndarray) -> np.ndarray:
            return _compress_one_perp_dual(full_mv(_lift_one_perp_coords(y)))
        return apply

    def _gram_mv(y: np.ndarray) -> np.ndarray:
        vals = np.asarray(y, dtype=np.float64)
        if vals.ndim == 1:
            return vals + np.sum(vals) * np.ones_like(vals)
        return vals + np.sum(vals, axis=0, keepdims=True)

    good_red_op = LinearOperator((reduced_n, reduced_n), matvec=_reduced_from_full(_good_mv), dtype=np.float64)
    bad_red_op = LinearOperator((reduced_n, reduced_n), matvec=_reduced_from_full(_bad_mv), dtype=np.float64)
    good_eps_red_op = LinearOperator((reduced_n, reduced_n), matvec=_reduced_from_full(_good_eps_mv), dtype=np.float64)
    gram_op = LinearOperator((reduced_n, reduced_n), matvec=_gram_mv, dtype=np.float64)

    rho_value, rho_coords, rho_resid = _solve_projected_extremal_mode(
        bad_red_op,
        largest=True,
        n=reduced_n,
        seed=1729,
        constraints=None,
        b_operator=good_eps_red_op,
        tol=tol,
        maxiter=maxiter,
    )
    lambda1_good, _vec_good, good_resid = _solve_projected_extremal_mode(
        good_red_op,
        largest=False,
        n=reduced_n,
        seed=1730,
        constraints=None,
        b_operator=gram_op,
        tol=tol,
        maxiter=maxiter,
    )
    lambda_max_bad, _vec_bad, bad_resid = _solve_projected_extremal_mode(
        bad_red_op,
        largest=True,
        n=reduced_n,
        seed=1731,
        constraints=None,
        b_operator=gram_op,
        tol=tol,
        maxiter=maxiter,
    )
    rho_vec = _project_mean_zero(_lift_one_perp_coords(rho_coords))

    rho_residual = _project_mean_zero(_bad_mv(rho_vec) - rho_value * _good_eps_mv(rho_vec))
    rho_residual_norm = float(np.linalg.norm(rho_residual))
    vector_diag = _vector_support_diagnostics(
        rho_vec,
        shell_levels=shell_levels,
        mode_keys=mode_keys,
        degree_good=np.asarray(setup["degree_good"], dtype=np.float64),
        degree_bad=np.asarray(setup["degree_bad"], dtype=np.float64),
    )
    source_diag = _rayleigh_source_breakdown(
        rho_vec,
        M_CC=M_CC,
        correction=correction,
        shell_levels=shell_levels,
        mode_keys=mode_keys,
        row_chunk=int(row_chunk),
    )
    sector_diag = None
    if audit_symmetry_sectors:
        sector_diag = _symmetry_sector_diagnostics(
            rho_vec,
            shell_levels=shell_levels,
            mode_keys=mode_keys,
            M_CC=M_CC,
            correction=correction,
            good_state=good_state,
            bad_state=bad_state,
        )
    angular_frame_diag = None
    if audit_angular_frame:
        angular_frame_diag = _extremizer_angular_frame_diagnostics(
            rho_vec,
            mode_keys=mode_keys,
        )

    return {
        "audit_requested": True,
        "dense_audit_available": False,
        "matrix_free_requested": True,
        "status": "ok",
        "decomposition": "S_C = L_good - L_bad",
        "row_chunk": int(row_chunk),
        "regularization_eps": float(eps),
        "L_good_lambda1_one_perp": float(lambda1_good - eps),
        "L_good_lambda1_one_perp_regularized": float(lambda1_good),
        "L_bad_lambda_max_one_perp": float(lambda_max_bad),
        "domination_ratio_sup_one_perp": float(rho_value),
        "domination_ratio_residual_norm": rho_residual_norm,
        "domination_ratio_solver_residual_norm": float(rho_resid),
        "L_good_solver_residual_norm": float(good_resid),
        "L_bad_solver_residual_norm": float(bad_resid),
        "domination_holds_strictly_observed": bool(rho_value < 1.0 + 1.0e-8),
        "worst_eigenvector_diagnostics": vector_diag,
        "symmetry_sector_diagnostics": sector_diag,
        "extremizer_angular_frame_diagnostics": angular_frame_diag,
        "source_decomposition": source_diag,
        "sign_statistics": setup["sign_stats"],
        "_rho_vec_full": rho_vec.tolist(),
    }


def _domination_ratio_masked_sector_diagnostics(
    *,
    n: int,
    M_CC: np.ndarray,
    correction: np.ndarray,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    full_diag: dict[str, Any] | None,
    mask: np.ndarray,
    sector_spec: dict[str, Any],
    row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    eps: float = DEFAULT_DOMINATION_EPS,
    tol: float = 1.0e-8,
    maxiter: int = 200,
    matvec_backend: str = "cpu",
    gpu_checks: int = 2,
) -> dict[str, Any]:
    selected = np.flatnonzero(np.asarray(mask, dtype=bool))
    sector_dim = int(len(selected))
    if sector_dim <= 1:
        return {
            "audit_requested": True,
            "status": "insufficient_sector_dimension",
            "sector_spec": sector_spec,
            "sector_dimension": sector_dim,
            "sector_reduced_dimension": max(sector_dim - 1, 0),
            "gpu_kn_authority": False,
        }

    M_sub = np.asarray(M_CC[np.ix_(selected, selected)], dtype=np.float64)
    correction_sub = np.asarray(correction[np.ix_(selected, selected)], dtype=np.float64)
    shell_sub = np.asarray(shell_levels[selected], dtype=np.float64)
    mode_keys_sub = [mode_keys[int(index)] for index in selected]

    backend_handle = _make_restricted_backend(
        M_CC=M_sub,
        correction=correction_sub,
        row_chunk=row_chunk,
        backend=matvec_backend,
        gpu_checks=gpu_checks,
    )
    reduced_n = sector_dim - 1
    try:
        def _good_mv(x: np.ndarray) -> np.ndarray:
            return backend_handle.good_mv(x)

        def _bad_mv(x: np.ndarray) -> np.ndarray:
            return backend_handle.bad_mv(x)

        def _good_eps_mv(x: np.ndarray) -> np.ndarray:
            vec = _project_mean_zero(np.asarray(x, dtype=np.float64))
            return _good_mv(vec) + float(eps) * vec

        def _reduced_from_full(full_mv):
            def apply(y: np.ndarray) -> np.ndarray:
                return _compress_one_perp_dual(full_mv(_lift_one_perp_coords(y)))
            return apply

        def _gram_mv(y: np.ndarray) -> np.ndarray:
            vals = np.asarray(y, dtype=np.float64)
            if vals.ndim == 1:
                return vals + np.sum(vals) * np.ones_like(vals)
            return vals + np.sum(vals, axis=0, keepdims=True)

        good_red_op = LinearOperator((reduced_n, reduced_n), matvec=_reduced_from_full(_good_mv), dtype=np.float64)
        bad_red_op = LinearOperator((reduced_n, reduced_n), matvec=_reduced_from_full(_bad_mv), dtype=np.float64)
        good_eps_red_op = LinearOperator((reduced_n, reduced_n), matvec=_reduced_from_full(_good_eps_mv), dtype=np.float64)
        gram_op = LinearOperator((reduced_n, reduced_n), matvec=_gram_mv, dtype=np.float64)

        rho_value, rho_coords, rho_resid = _solve_projected_extremal_mode(
            bad_red_op,
            largest=True,
            n=reduced_n,
            seed=2718,
            constraints=None,
            b_operator=good_eps_red_op,
            tol=tol,
            maxiter=maxiter,
        )
        rho_vec_sub = _project_mean_zero(_lift_one_perp_coords(rho_coords))
        lambda1_good, _vec_good, good_resid = _solve_projected_extremal_mode(
            good_red_op,
            largest=False,
            n=reduced_n,
            seed=2719,
            constraints=None,
            b_operator=gram_op,
            tol=tol,
            maxiter=maxiter,
        )
        lambda_max_bad, _vec_bad, bad_resid = _solve_projected_extremal_mode(
            bad_red_op,
            largest=True,
            n=reduced_n,
            seed=2720,
            constraints=None,
            b_operator=gram_op,
            tol=tol,
            maxiter=maxiter,
        )
        residual = _project_mean_zero(_bad_mv(rho_vec_sub) - rho_value * _good_eps_mv(rho_vec_sub))
        rho_residual_norm = float(np.linalg.norm(residual))

        rho_vec_full = np.zeros(len(mode_keys), dtype=np.float64)
        rho_vec_full[selected] = rho_vec_sub
        rho_vec_full = _project_mean_zero(rho_vec_full)
        rho_vec_full /= max(float(np.linalg.norm(rho_vec_full)), 1.0e-300)

        vector_diag = _vector_support_diagnostics(
            rho_vec_sub,
            shell_levels=shell_sub,
            mode_keys=mode_keys_sub,
            degree_good=np.sum(np.maximum(-(M_sub - correction_sub), 0.0), axis=1),
            degree_bad=np.sum(np.maximum(M_sub - correction_sub, 0.0), axis=1),
        )

        overlap_diag: dict[str, Any] = {
            "full_extremizer_sector_mass": None,
            "full_extremizer_sector_projected_overlap": None,
            "rho_gap_to_full": None,
            "rho_ratio_to_full": None,
        }
        if full_diag is not None:
            full_rho = full_diag.get("domination_ratio_sup_one_perp")
            full_vec = full_diag.get("_rho_vec_full")
            if full_vec is not None:
                full_unit = np.asarray(full_vec, dtype=np.float64)
                full_unit /= max(float(np.linalg.norm(full_unit)), 1.0e-300)
                overlap_diag["full_extremizer_sector_mass"] = float(np.sum(full_unit[selected] ** 2))
                full_proj = np.zeros_like(full_unit)
                full_proj[selected] = full_unit[selected]
                full_proj = _project_mean_zero(full_proj)
                full_proj_norm = float(np.linalg.norm(full_proj))
                if full_proj_norm > 1.0e-14:
                    full_proj /= full_proj_norm
                    overlap_diag["full_extremizer_sector_projected_overlap"] = float(abs(full_proj @ rho_vec_full))
            if full_rho is not None:
                overlap_diag["rho_gap_to_full"] = float(full_rho - rho_value)
                overlap_diag["rho_ratio_to_full"] = float(rho_value / full_rho) if abs(full_rho) > 1.0e-14 else None

        source_diag = _rayleigh_source_breakdown(
            rho_vec_sub,
            M_CC=M_sub,
            correction=correction_sub,
            shell_levels=shell_sub,
            mode_keys=mode_keys_sub,
            row_chunk=min(int(row_chunk), max(1, sector_dim)),
        )

        return {
            "audit_requested": True,
            "status": "ok",
            "sector_spec": sector_spec,
            "sector_dimension": sector_dim,
            "sector_reduced_dimension": reduced_n,
            "matvec_backend": backend_handle.name,
            "gpu_kn_authority": False,
            "L_good_lambda1_one_perp": float(lambda1_good - eps),
            "L_good_lambda1_one_perp_regularized": float(lambda1_good),
            "L_bad_lambda_max_one_perp": float(lambda_max_bad),
            "domination_ratio_sup_one_perp": float(rho_value),
            "domination_ratio_residual_norm": rho_residual_norm,
            "domination_ratio_solver_residual_norm": float(rho_resid),
            "L_good_solver_residual_norm": float(good_resid),
            "L_bad_solver_residual_norm": float(bad_resid),
            "domination_holds_strictly_observed": bool(rho_value < 1.0 + 1.0e-8),
            "worst_eigenvector_diagnostics": vector_diag,
            "source_decomposition": source_diag,
            "full_comparison": overlap_diag,
            **backend_handle.info,
        }
    finally:
        backend_handle.close()


def _domination_ratio_restricted_sector_diagnostics(
    *,
    n: int,
    M_CC: np.ndarray,
    correction: np.ndarray,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    full_diag: dict[str, Any] | None,
    row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    eps: float = DEFAULT_DOMINATION_EPS,
    tol: float = 1.0e-8,
    maxiter: int = 200,
    nonaxis_only: bool = True,
    orbit_labels: list[str] | None = None,
    matvec_backend: str = "cpu",
    gpu_checks: int = 2,
) -> dict[str, Any]:
    mask, sector_spec = _restricted_sector_mask(
        n=n,
        mode_keys=mode_keys,
        include_nonaxis_only=nonaxis_only,
        orbit_labels=orbit_labels,
    )
    return _domination_ratio_masked_sector_diagnostics(
        n=n,
        M_CC=M_CC,
        correction=correction,
        shell_levels=shell_levels,
        mode_keys=mode_keys,
        full_diag=full_diag,
        mask=mask,
        sector_spec=sector_spec,
        row_chunk=row_chunk,
        eps=eps,
        tol=tol,
        maxiter=maxiter,
        matvec_backend=matvec_backend,
        gpu_checks=gpu_checks,
    )


def _halo_energy_capture_metrics(
    *,
    full_vec: np.ndarray,
    selected: np.ndarray,
    total: np.ndarray,
) -> dict[str, Any]:
    full_unit = np.asarray(full_vec, dtype=np.float64)
    full_unit /= max(float(np.linalg.norm(full_unit)), 1.0e-300)
    x_sector = np.zeros_like(full_unit)
    x_sector[selected] = full_unit[selected]

    good_w = np.maximum(-np.asarray(total, dtype=np.float64), 0.0)
    bad_w = np.maximum(np.asarray(total, dtype=np.float64), 0.0)
    np.fill_diagonal(good_w, 0.0)
    np.fill_diagonal(bad_w, 0.0)

    diff = full_unit[:, None] - full_unit[None, :]
    diff_sq = diff * diff
    mask_mat = np.zeros_like(good_w, dtype=bool)
    mask_mat[np.ix_(selected, selected)] = True
    cross_mat = np.zeros_like(good_w, dtype=bool)
    outside = ~selected
    cross_mat[np.ix_(selected, outside)] = True
    cross_mat[np.ix_(outside, selected)] = True

    good_total = 0.5 * float(np.sum(good_w * diff_sq))
    bad_total = 0.5 * float(np.sum(bad_w * diff_sq))
    good_internal = 0.5 * float(np.sum(good_w[mask_mat] * diff_sq[mask_mat]))
    bad_internal = 0.5 * float(np.sum(bad_w[mask_mat] * diff_sq[mask_mat]))
    good_cross = 0.5 * float(np.sum(good_w[cross_mat] * diff_sq[cross_mat]))
    bad_cross = 0.5 * float(np.sum(bad_w[cross_mat] * diff_sq[cross_mat]))

    def _ratio(num: float, den: float) -> float | None:
        return float(num / den) if den > 1.0e-14 else None

    sector_mass = float(np.sum(full_unit[selected] ** 2))
    return {
        "full_extremizer_sector_mass": sector_mass,
        "good_energy_capture": _ratio(good_internal, good_total),
        "bad_energy_capture": _ratio(bad_internal, bad_total),
        "good_boundary_flux_ratio": _ratio(good_cross, good_internal + good_cross),
        "bad_boundary_flux_ratio": _ratio(bad_cross, bad_internal + bad_cross),
        "boundary_flux_ratio": _ratio(good_cross + bad_cross, good_internal + bad_internal + good_cross + bad_cross),
        "sector_vector_mass_capture": _ratio(float(np.dot(x_sector, x_sector)), float(np.dot(full_unit, full_unit))),
    }


def _domination_halo_growth_diagnostics(
    *,
    n: int,
    M_CC: np.ndarray,
    correction: np.ndarray,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    full_diag: dict[str, Any] | None,
    row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    eps: float = DEFAULT_DOMINATION_EPS,
    tol: float = 1.0e-8,
    maxiter: int = 200,
    nonaxis_only: bool = True,
    orbit_labels: list[str] | None = None,
    matvec_backend: str = "cpu",
    gpu_checks: int = 2,
    support_tol: float = 1.0e-12,
    max_radius: int = 6,
    rho_match_factor: float = 1.02,
    overlap_target: float = 0.90,
    boundary_flux_target: float = 0.05,
) -> dict[str, Any]:
    seed_mask, seed_spec = _restricted_sector_mask(
        n=n,
        mode_keys=mode_keys,
        include_nonaxis_only=nonaxis_only,
        orbit_labels=orbit_labels,
    )
    if not np.any(seed_mask):
        return {
            "audit_requested": True,
            "status": "empty_seed",
            "seed_spec": seed_spec,
            "gpu_kn_authority": False,
        }

    total = np.asarray(M_CC - correction, dtype=np.float64)
    allowed_mask = np.ones(len(mode_keys), dtype=bool)
    if nonaxis_only:
        allowed_mask &= ~np.asarray([_is_axis_mode(key) for key in mode_keys], dtype=bool)
        seed_mask &= allowed_mask
    adjacency = _schur_support_adjacency(total, support_tol=support_tol, allowed_mask=allowed_mask)
    masks = _expand_halo_radius(adjacency, seed_mask, max_radius=max_radius)

    full_rho = None if full_diag is None else full_diag.get("domination_ratio_sup_one_perp")
    full_vec = None if full_diag is None else full_diag.get("_rho_vec_full")
    radius_rows: list[dict[str, Any]] = []
    best_radius: dict[str, Any] | None = None
    previous_count = -1

    for radius, mask in enumerate(masks):
        mask = np.asarray(mask, dtype=bool)
        count = int(np.sum(mask))
        if count == previous_count and radius > 0:
            continue
        previous_count = count
        sector_spec = {
            "type": "halo_growth",
            "radius": int(radius),
            "support_tol": float(support_tol),
            "nonaxis_only": bool(nonaxis_only),
            "seed_spec": seed_spec,
            "selected_mode_count": count,
        }
        diag = _domination_ratio_masked_sector_diagnostics(
            n=n,
            M_CC=M_CC,
            correction=correction,
            shell_levels=shell_levels,
            mode_keys=mode_keys,
            full_diag=full_diag,
            mask=mask,
            sector_spec=sector_spec,
            row_chunk=row_chunk,
            eps=eps,
            tol=tol,
            maxiter=maxiter,
            matvec_backend=matvec_backend,
            gpu_checks=gpu_checks,
        )
        row = {
            "radius": int(radius),
            "sector_dimension": count,
            "status": diag.get("status"),
        }
        if diag.get("status") == "ok":
            full_cmp = diag.get("full_comparison") or {}
            row.update(
                {
                    "domination_ratio_sup_one_perp": diag.get("domination_ratio_sup_one_perp"),
                    "rho_ratio_to_full": full_cmp.get("rho_ratio_to_full"),
                    "full_extremizer_sector_projected_overlap": full_cmp.get("full_extremizer_sector_projected_overlap"),
                    "full_extremizer_sector_mass": full_cmp.get("full_extremizer_sector_mass"),
                    "matvec_backend": diag.get("matvec_backend"),
                }
            )
            if full_vec is not None:
                row.update(
                    _halo_energy_capture_metrics(
                        full_vec=np.asarray(full_vec, dtype=np.float64),
                        selected=np.flatnonzero(mask),
                        total=total,
                    )
                )
            meets_match = (
                row.get("rho_ratio_to_full") is not None
                and row["rho_ratio_to_full"] <= float(rho_match_factor)
            )
            meets_overlap = (
                row.get("full_extremizer_sector_projected_overlap") is not None
                and row["full_extremizer_sector_projected_overlap"] >= float(overlap_target)
            )
            meets_boundary = (
                row.get("boundary_flux_ratio") is not None
                and row["boundary_flux_ratio"] <= float(boundary_flux_target)
            )
            row["stop_criteria_satisfied"] = bool(meets_match and meets_overlap and meets_boundary)
            if best_radius is None and row["stop_criteria_satisfied"]:
                best_radius = row
        radius_rows.append(row)

    return {
        "audit_requested": True,
        "status": "ok",
        "seed_spec": seed_spec,
        "support_tol": float(support_tol),
        "max_radius": int(max_radius),
        "rho_match_factor": float(rho_match_factor),
        "overlap_target": float(overlap_target),
        "boundary_flux_target": float(boundary_flux_target),
        "full_rho": float(full_rho) if full_rho is not None else None,
        "radii": radius_rows,
        "best_radius": best_radius,
        "gpu_kn_authority": False,
        "gpu_domination_scout_installed": bool(
            any(row.get("matvec_backend") == "torch-gpu-scout" for row in radius_rows)
        ),
    }


def _domination_coarse_quotient_diagnostics(
    *,
    n: int,
    M_CC: np.ndarray,
    correction: np.ndarray,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    full_diag: dict[str, Any] | None,
    nonaxis_only: bool = True,
    scheme: str = "shell-zero-orbit",
    tol: float = 1.0e-10,
) -> dict[str, Any]:
    allowed = np.ones(len(mode_keys), dtype=bool)
    if nonaxis_only:
        allowed &= ~np.asarray([_is_axis_mode(key) for key in mode_keys], dtype=bool)
    selected = np.flatnonzero(allowed)
    if selected.size <= 1:
        return {
            "audit_requested": True,
            "status": "insufficient_sector_dimension",
            "gpu_kn_authority": False,
            "nonaxis_only": bool(nonaxis_only),
            "scheme": scheme,
        }

    total_sub = np.asarray(
        M_CC[np.ix_(selected, selected)] - correction[np.ix_(selected, selected)],
        dtype=np.float64,
    )
    shell_sub = np.asarray(shell_levels[selected], dtype=np.int64)
    keys_sub = [mode_keys[int(index)] for index in selected]
    class_per_mode = [
        _coarse_quotient_class_label(shell=int(shell_sub[idx]), key=keys_sub[idx], scheme=scheme)
        for idx in range(len(keys_sub))
    ]
    q_cls, class_labels, class_dims = _orthonormal_indicator_basis(class_per_mode)
    class_count = int(len(class_labels))
    if class_count <= 1:
        return {
            "audit_requested": True,
            "status": "insufficient_class_count",
            "gpu_kn_authority": False,
            "nonaxis_only": bool(nonaxis_only),
            "scheme": scheme,
            "sector_dimension": int(selected.size),
            "class_count": class_count,
        }

    L_good, L_bad = _dense_signed_laplacians(total_sub)
    A = np.asarray(q_cls.T @ L_bad @ q_cls, dtype=np.float64)
    B = np.asarray(q_cls.T @ L_good @ q_cls, dtype=np.float64)

    q_const = q_cls.T @ np.ones(len(selected), dtype=np.float64)
    p = _orth_basis_complement(q_const)
    if p.shape[1] == 0:
        return {
            "audit_requested": True,
            "status": "trivial_class_one_perp",
            "gpu_kn_authority": False,
            "nonaxis_only": bool(nonaxis_only),
            "scheme": scheme,
            "sector_dimension": int(selected.size),
            "class_count": class_count,
        }

    A_red = np.asarray(p.T @ A @ p, dtype=np.float64)
    B_red = np.asarray(p.T @ B @ p, dtype=np.float64)
    evals_B = _sym_eigvals(B_red)
    lambda1_good = float(np.min(evals_B)) if evals_B.size else None
    if lambda1_good is None or lambda1_good <= float(tol):
        return {
            "audit_requested": True,
            "status": "quotient_good_singular",
            "gpu_kn_authority": False,
            "nonaxis_only": bool(nonaxis_only),
            "scheme": scheme,
            "sector_dimension": int(selected.size),
            "class_count": class_count,
            "quotient_lambda1_good": lambda1_good,
        }

    eigvals, eigvecs = eigh(A_red, B_red, driver="gvd")
    idx = int(np.argmax(eigvals))
    rho = float(eigvals[idx])
    z = np.asarray(eigvecs[:, idx], dtype=np.float64)
    class_coeff = np.asarray(p @ z, dtype=np.float64)
    lifted = np.asarray(q_cls @ class_coeff, dtype=np.float64)
    lifted = _project_mean_zero(lifted)
    lifted /= max(float(np.linalg.norm(lifted)), 1.0e-300)

    residual = _project_mean_zero(L_bad @ lifted - rho * (L_good @ lifted))
    residual_norm = float(np.linalg.norm(residual))

    full_cmp: dict[str, Any] = {
        "rho_gap_to_full": None,
        "rho_ratio_to_full": None,
        "full_extremizer_sector_mass": None,
        "full_extremizer_projected_overlap": None,
        "lifted_vector_residual_norm": residual_norm,
    }
    class_mass: dict[str, float] = {}
    lifted_mass: dict[str, float] = {}
    top_classes: list[dict[str, Any]] = []
    if full_diag is not None and full_diag.get("_rho_vec_full") is not None:
        full_vec = np.asarray(full_diag["_rho_vec_full"], dtype=np.float64)
        full_vec = full_vec[selected]
        full_vec = _project_mean_zero(full_vec)
        full_vec /= max(float(np.linalg.norm(full_vec)), 1.0e-300)
        full_mass = full_vec * full_vec
        for label, count in zip(class_labels, class_dims):
            mask = np.asarray([entry == label for entry in class_per_mode], dtype=bool)
            class_mass[label] = float(np.sum(full_mass[mask]))
            lifted_mass[label] = float(np.sum((lifted[mask] ** 2)))
        full_cmp["full_extremizer_sector_mass"] = 1.0
        full_cmp["full_extremizer_projected_overlap"] = float(abs(full_vec @ lifted))
        full_rho = full_diag.get("domination_ratio_sup_one_perp")
        if full_rho is not None:
            full_cmp["rho_gap_to_full"] = float(full_rho - rho)
            full_cmp["rho_ratio_to_full"] = float(rho / full_rho) if abs(full_rho) > 1.0e-14 else None

        ranked = sorted(class_labels, key=lambda label: (-class_mass.get(label, 0.0), label))
        for rank, label in enumerate(ranked[:20], start=1):
            top_classes.append(
                {
                    "rank": int(rank),
                    "class_label": label,
                    "dimension": int(class_dims[class_labels.index(label)]),
                    "full_extremizer_mass": float(class_mass.get(label, 0.0)),
                    "lifted_quotient_mass": float(lifted_mass.get(label, 0.0)),
                }
            )

    return {
        "audit_requested": True,
        "status": "ok",
        "gpu_kn_authority": False,
        "nonaxis_only": bool(nonaxis_only),
        "scheme": scheme,
        "sector_dimension": int(selected.size),
        "class_count": class_count,
        "quotient_lambda1_good": lambda1_good,
        "quotient_lambda_max_bad": float(np.max(_sym_eigvals(A_red))) if A_red.size else None,
        "quotient_domination_ratio_sup_one_perp": rho,
        "quotient_domination_holds_strictly_observed": bool(rho < 1.0 + 1.0e-8),
        "quotient_residual_norm": residual_norm,
        "class_labels": class_labels,
        "class_dimensions": [int(v) for v in class_dims.tolist()],
        "full_extremizer_class_mass": class_mass,
        "lifted_quotient_class_mass": lifted_mass,
        "top_classes_by_full_extremizer_mass": top_classes,
        "good_energy_matrix": B.tolist(),
        "bad_energy_matrix": A.tolist(),
        "full_comparison": full_cmp,
    }


def _domination_row_pairing_diagnostics(
    *,
    M_CC: np.ndarray,
    correction: np.ndarray,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    full_diag: dict[str, Any] | None,
    row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    tol: float = 1.0e-10,
    maxiter: int = 200,
) -> dict[str, Any]:
    n = int(M_CC.shape[0])
    if n <= 1:
        return {
            "audit_requested": True,
            "status": "trivial",
            "gpu_kn_authority": False,
        }

    setup = _build_chunked_signed_laplacian_state(M_CC, correction, row_chunk=row_chunk)
    degree_good = np.asarray(setup["degree_good"], dtype=np.float64)
    degree_bad = np.asarray(setup["degree_bad"], dtype=np.float64)
    good_state = _ChunkedSignedLaplacian("good", degree_good, int(row_chunk))
    bad_state = _ChunkedSignedLaplacian("bad", degree_bad, int(row_chunk))

    safe_ratio = lambda num, den: (float(num / den) if den > 1.0e-14 else None)

    row_bad_good_ratio = np.full(n, np.inf, dtype=np.float64)
    positive_good = degree_good > 1.0e-14
    row_bad_good_ratio[positive_good] = degree_bad[positive_good] / degree_good[positive_good]
    zero_good_zero_bad = (~positive_good) & (degree_bad <= 1.0e-14)
    row_bad_good_ratio[zero_good_zero_bad] = 0.0

    row_3bad_2good_ratio = np.full(n, np.inf, dtype=np.float64)
    positive_two_good = (2.0 * degree_good) > 1.0e-14
    row_3bad_2good_ratio[positive_two_good] = (3.0 * degree_bad[positive_two_good]) / (
        2.0 * degree_good[positive_two_good]
    )
    zero_two_good_zero_bad = (~positive_two_good) & (degree_bad <= 1.0e-14)
    row_3bad_2good_ratio[zero_two_good_zero_bad] = 0.0

    def _row_summary(order_metric: np.ndarray, metric_name: str) -> list[dict[str, Any]]:
        finite_order = np.argsort(
            np.where(np.isfinite(order_metric), -order_metric, -1.0e308)
        )
        rows: list[dict[str, Any]] = []
        for rank, idx in enumerate(finite_order[:20], start=1):
            index = int(idx)
            rows.append(
                {
                    "rank": int(rank),
                    "index": index,
                    "mode": [int(v) for v in mode_keys[index]],
                    "shell": int(shell_levels[index]),
                    "is_axis": bool(_is_axis_mode(mode_keys[index])),
                    "degree_good": float(degree_good[index]),
                    "degree_bad": float(degree_bad[index]),
                    "row_bad_good_ratio": (
                        float(row_bad_good_ratio[index]) if np.isfinite(row_bad_good_ratio[index]) else None
                    ),
                    "row_3bad_2good_ratio": (
                        float(row_3bad_2good_ratio[index])
                        if np.isfinite(row_3bad_2good_ratio[index])
                        else None
                    ),
                    "sort_metric": metric_name,
                }
            )
        return rows

    q_offdiag_positive = 0
    q_offdiag_negative = 0
    q_max_positive_offdiag = 0.0
    q_min_negative_offdiag = 0.0
    q_row_sum_max_abs = 0.0
    q_min_diag = float("inf")
    q_max_diag = float("-inf")
    q_negative_diag_count = 0
    q_positive_diag_count = 0
    q_gershgorin_lower_bound = float("inf")
    q_gershgorin_upper_bound = float("-inf")

    for start in range(0, n, row_chunk):
        stop = min(start + row_chunk, n)
        total_chunk = np.asarray(M_CC[start:stop, :] - correction[start:stop, :], dtype=np.float64)
        good_weights = np.maximum(-total_chunk, 0.0)
        bad_weights = np.maximum(total_chunk, 0.0)
        diag_rows = np.arange(stop - start, dtype=np.int64)
        diag_cols = np.arange(start, stop, dtype=np.int64) - start
        good_weights[diag_rows, diag_cols] = 0.0
        bad_weights[diag_rows, diag_cols] = 0.0

        q_diag = 2.0 * np.sum(good_weights, axis=1) - 3.0 * np.sum(bad_weights, axis=1)
        q_offdiag = -2.0 * good_weights + 3.0 * bad_weights
        q_offdiag[diag_rows, diag_cols] = 0.0
        row_abs_sum = np.sum(np.abs(q_offdiag), axis=1)
        row_sum = q_diag + np.sum(q_offdiag, axis=1)

        q_row_sum_max_abs = max(q_row_sum_max_abs, float(np.max(np.abs(row_sum))))
        q_min_diag = min(q_min_diag, float(np.min(q_diag)))
        q_max_diag = max(q_max_diag, float(np.max(q_diag)))
        q_negative_diag_count += int(np.sum(q_diag < -tol))
        q_positive_diag_count += int(np.sum(q_diag > tol))
        q_gershgorin_lower_bound = min(
            q_gershgorin_lower_bound,
            float(np.min(q_diag - row_abs_sum)),
        )
        q_gershgorin_upper_bound = max(
            q_gershgorin_upper_bound,
            float(np.max(q_diag + row_abs_sum)),
        )

        pos_mask = q_offdiag > tol
        neg_mask = q_offdiag < -tol
        q_offdiag_positive += int(np.sum(pos_mask))
        q_offdiag_negative += int(np.sum(neg_mask))
        if np.any(pos_mask):
            q_max_positive_offdiag = max(q_max_positive_offdiag, float(np.max(q_offdiag[pos_mask])))
        if np.any(neg_mask):
            q_min_negative_offdiag = min(q_min_negative_offdiag, float(np.min(q_offdiag[neg_mask])))

    reduced_n = n - 1

    def _good_mv(x: np.ndarray) -> np.ndarray:
        return _signed_laplacian_apply(x, M_CC=M_CC, correction=correction, state=good_state)

    def _bad_mv(x: np.ndarray) -> np.ndarray:
        return _signed_laplacian_apply(x, M_CC=M_CC, correction=correction, state=bad_state)

    def _q_mv(x: np.ndarray) -> np.ndarray:
        vec = _project_mean_zero(np.asarray(x, dtype=np.float64))
        return _project_mean_zero(2.0 * _good_mv(vec) - 3.0 * _bad_mv(vec))

    def _reduced_from_full(full_mv):
        def apply(y: np.ndarray) -> np.ndarray:
            return _compress_one_perp_dual(full_mv(_lift_one_perp_coords(y)))
        return apply

    def _gram_mv(y: np.ndarray) -> np.ndarray:
        vals = np.asarray(y, dtype=np.float64)
        if vals.ndim == 1:
            return vals + np.sum(vals) * np.ones_like(vals)
        return vals + np.sum(vals, axis=0, keepdims=True)

    q_red_op = LinearOperator((reduced_n, reduced_n), matvec=_reduced_from_full(_q_mv), dtype=np.float64)
    gram_op = LinearOperator((reduced_n, reduced_n), matvec=_gram_mv, dtype=np.float64)
    lambda_min_q, q_coords, q_resid = _solve_projected_extremal_mode(
        q_red_op,
        largest=False,
        n=reduced_n,
        seed=31415,
        constraints=None,
        b_operator=gram_op,
        tol=tol,
        maxiter=maxiter,
    )
    q_vec = _project_mean_zero(_lift_one_perp_coords(q_coords))
    q_residual = _project_mean_zero(_q_mv(q_vec) - lambda_min_q * q_vec)
    q_residual_norm = float(np.linalg.norm(q_residual))
    q_vec_diag = _vector_support_diagnostics(
        q_vec,
        shell_levels=shell_levels,
        mode_keys=mode_keys,
        degree_good=degree_good,
        degree_bad=degree_bad,
    )

    extremizer_weighted_ratio = None
    extremizer_row_mass_top: list[dict[str, Any]] = []
    if full_diag is not None and full_diag.get("_rho_vec_full") is not None:
        rho_vec = np.asarray(full_diag["_rho_vec_full"], dtype=np.float64)
        rho_vec /= max(float(np.linalg.norm(rho_vec)), 1.0e-300)
        rho_mass = rho_vec * rho_vec
        finite_mask = np.isfinite(row_3bad_2good_ratio)
        if np.any(finite_mask):
            extremizer_weighted_ratio = float(np.sum(rho_mass[finite_mask] * row_3bad_2good_ratio[finite_mask]))
        top_idx = np.argsort(-rho_mass)[:20]
        for rank, idx in enumerate(top_idx, start=1):
            index = int(idx)
            extremizer_row_mass_top.append(
                {
                    "rank": int(rank),
                    "index": index,
                    "mode": [int(v) for v in mode_keys[index]],
                    "shell": int(shell_levels[index]),
                    "mass": float(rho_mass[index]),
                    "row_bad_good_ratio": (
                        float(row_bad_good_ratio[index]) if np.isfinite(row_bad_good_ratio[index]) else None
                    ),
                    "row_3bad_2good_ratio": (
                        float(row_3bad_2good_ratio[index])
                        if np.isfinite(row_3bad_2good_ratio[index])
                        else None
                    ),
                }
            )

    finite_bad_good = row_bad_good_ratio[np.isfinite(row_bad_good_ratio)]
    finite_3bad_2good = row_3bad_2good_ratio[np.isfinite(row_3bad_2good_ratio)]

    return {
        "audit_requested": True,
        "status": "ok",
        "gpu_kn_authority": False,
        "row_chunk": int(row_chunk),
        "Q_definition": "Q = 2L_good - 3L_bad",
        "Q_row_sum_max_abs": q_row_sum_max_abs,
        "Q_lambda_min_one_perp": float(lambda_min_q),
        "Q_solver_residual_norm": float(q_resid),
        "Q_residual_norm": q_residual_norm,
        "Q_psd_observed_on_one_perp": bool(lambda_min_q >= -1.0e-8),
        "Q_worst_eigenvector_diagnostics": q_vec_diag,
        "Q_sign_diagnostics": {
            "num_positive_offdiag": int(q_offdiag_positive),
            "num_negative_offdiag": int(q_offdiag_negative),
            "max_positive_offdiag": float(q_max_positive_offdiag),
            "min_negative_offdiag": float(q_min_negative_offdiag),
            "min_diag": float(q_min_diag),
            "max_diag": float(q_max_diag),
            "negative_diag_count": int(q_negative_diag_count),
            "positive_diag_count": int(q_positive_diag_count),
            "ordinary_laplacian_candidate": bool(q_offdiag_positive == 0 and q_min_diag >= -tol),
            "gershgorin_lower_bound": float(q_gershgorin_lower_bound),
            "gershgorin_upper_bound": float(q_gershgorin_upper_bound),
        },
        "max_row_bad_good_ratio": (
            float(np.max(finite_bad_good)) if finite_bad_good.size else None
        ),
        "mean_row_bad_good_ratio": (
            float(np.mean(finite_bad_good)) if finite_bad_good.size else None
        ),
        "max_row_3bad_2good_ratio": (
            float(np.max(finite_3bad_2good)) if finite_3bad_2good.size else None
        ),
        "mean_row_3bad_2good_ratio": (
            float(np.mean(finite_3bad_2good)) if finite_3bad_2good.size else None
        ),
        "rows_with_3bad_2good_ratio_above_one": int(np.sum(row_3bad_2good_ratio > 1.0 + 1.0e-12)),
        "worst_rows_by_3bad_2good_ratio": _row_summary(row_3bad_2good_ratio, "row_3bad_2good_ratio"),
        "worst_rows_by_bad_good_ratio": _row_summary(row_bad_good_ratio, "row_bad_good_ratio"),
        "extremizer_mass_weighted_row_3bad_2good_ratio": extremizer_weighted_ratio,
        "extremizer_top_rows": extremizer_row_mass_top,
        "_q_bottom_vec_full": q_vec.tolist(),
    }


def _q_helical_lift_diagnostics(
    *,
    M_CC: np.ndarray,
    correction: np.ndarray,
    shell_levels: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    rho_vec: np.ndarray | None,
    q_bottom_vec: np.ndarray | None,
    row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    tol: float = 1.0e-10,
) -> dict[str, Any]:
    """Candidate helical-channel lift of Q = 2L_good - 3L_bad.

    This is explicitly observational. The current Q acts on scalar seam amplitudes,
    so this audit does not identify Q with a Waleffe triad operator and does not
    expose the full 8 helical triad sign sectors.
    """
    n = int(M_CC.shape[0])
    if n <= 1:
        return {
            "audit_requested": True,
            "status": "trivial",
            "gpu_kn_authority": False,
            "helical_basis_constructed": False,
        }

    h_plus, h_minus = _canonical_helical_frames(mode_keys)

    def _q_chunk(start: int, stop: int) -> np.ndarray:
        total_chunk = np.asarray(M_CC[start:stop, :] - correction[start:stop, :], dtype=np.float64)
        good_weights = np.maximum(-total_chunk, 0.0)
        bad_weights = np.maximum(total_chunk, 0.0)
        diag_rows = np.arange(stop - start, dtype=np.int64)
        diag_cols = np.arange(start, stop, dtype=np.int64) - start
        good_weights[diag_rows, diag_cols] = 0.0
        bad_weights[diag_rows, diag_cols] = 0.0
        q_diag = 2.0 * np.sum(good_weights, axis=1) - 3.0 * np.sum(bad_weights, axis=1)
        q_offdiag = -2.0 * good_weights + 3.0 * bad_weights
        q_offdiag[diag_rows, diag_cols] = 0.0
        q_offdiag[diag_rows, diag_cols] = q_diag
        return q_offdiag

    block_sq = {"++": 0.0, "+-": 0.0, "-+": 0.0, "--": 0.0}
    total_sq = 0.0
    gram_symmetry_defect = {"++": 0.0, "+-": 0.0, "-+": 0.0, "--": 0.0}
    scalar_trace = 0.0

    if rho_vec is not None and np.size(rho_vec):
        rho_vec = _project_mean_zero(np.asarray(rho_vec, dtype=np.float64))
        rho_vec /= max(float(np.linalg.norm(rho_vec)), 1.0e-300)
    else:
        rho_vec = None
    if q_bottom_vec is not None and np.size(q_bottom_vec):
        q_vec = _project_mean_zero(np.asarray(q_bottom_vec, dtype=np.float64))
        q_vec /= max(float(np.linalg.norm(q_vec)), 1.0e-300)
    else:
        q_vec = None

    rayleigh_on_vectors: dict[str, dict[str, float | None]] = {}

    def _accumulate_rayleigh(label: str, vec: np.ndarray | None) -> None:
        if vec is None:
            return
        if label not in rayleigh_on_vectors:
            rayleigh_on_vectors[label] = {"++": 0.0, "+-": 0.0, "-+": 0.0, "--": 0.0}
        vals = rayleigh_on_vectors[label]
        assert vals is not None
        for start in range(0, n, row_chunk):
            stop = min(start + row_chunk, n)
            q_chunk = _q_chunk(start, stop)
            hp_chunk = h_plus[start:stop, :]
            hm_chunk = h_minus[start:stop, :]
            g_pp = np.real(hp_chunk.conj() @ h_plus.T)
            g_pm = np.real(hp_chunk.conj() @ h_minus.T)
            g_mp = np.real(hm_chunk.conj() @ h_plus.T)
            g_mm = np.real(hm_chunk.conj() @ h_minus.T)
            v_chunk = vec[start:stop]
            vals["++"] += float(v_chunk @ ((q_chunk * g_pp) @ vec))
            vals["+-"] += float(v_chunk @ ((q_chunk * g_pm) @ vec))
            vals["-+"] += float(v_chunk @ ((q_chunk * g_mp) @ vec))
            vals["--"] += float(v_chunk @ ((q_chunk * g_mm) @ vec))

    for start in range(0, n, row_chunk):
        stop = min(start + row_chunk, n)
        q_chunk = _q_chunk(start, stop)
        total_sq += float(np.sum(q_chunk * q_chunk))
        scalar_trace += float(np.trace(q_chunk[:, start:stop]))

        hp_chunk = h_plus[start:stop, :]
        hm_chunk = h_minus[start:stop, :]
        g_pp = np.real(hp_chunk.conj() @ h_plus.T)
        g_pm = np.real(hp_chunk.conj() @ h_minus.T)
        g_mp = np.real(hm_chunk.conj() @ h_plus.T)
        g_mm = np.real(hm_chunk.conj() @ h_minus.T)

        blocks = {
            "++": q_chunk * g_pp,
            "+-": q_chunk * g_pm,
            "-+": q_chunk * g_mp,
            "--": q_chunk * g_mm,
        }
        for label, block in blocks.items():
            block_sq[label] += float(np.sum(block * block))
        local_pp = g_pp[:, start:stop]
        local_pm = g_pm[:, start:stop]
        local_mp = g_mp[:, start:stop]
        local_mm = g_mm[:, start:stop]
        gram_symmetry_defect["++"] += float(np.sum((local_pp - local_pp.T) ** 2))
        gram_symmetry_defect["--"] += float(np.sum((local_mm - local_mm.T) ** 2))
        gram_symmetry_defect["+-"] += float(np.sum((local_pm - local_mp.T) ** 2))
        gram_symmetry_defect["-+"] += float(np.sum((local_mp - local_pm.T) ** 2))

    _accumulate_rayleigh("rho_extremizer", rho_vec)
    _accumulate_rayleigh("q_bottom_mode", q_vec)

    total_fro = math.sqrt(max(total_sq, 0.0))
    block_fro = {label: math.sqrt(max(value, 0.0)) for label, value in block_sq.items()}
    diag_fro = math.sqrt(max(block_sq["++"] + block_sq["--"], 0.0))
    off_fro = math.sqrt(max(block_sq["+-"] + block_sq["-+"], 0.0))

    relevance_observed = bool(total_fro > 1.0e-14 and off_fro / total_fro < 0.95)
    approx_block_diag = bool(total_fro > 1.0e-14 and off_fro / total_fro <= 0.10)

    return {
        "audit_requested": True,
        "status": "ok",
        "gpu_kn_authority": False,
        "helical_basis_constructed": True,
        "current_phase_Q_projected_into_helical_basis": True,
        "candidate_lift_only": True,
        "q_equals_waleffe_triad_operator_proved": False,
        "full_waleffe_eight_sector_available": False,
        "helical_channel_sector_count": 2,
        "note": (
            "Current DASHI Q acts on scalar seam amplitudes. This audit builds a "
            "candidate canonical helical-channel lift and measures channel-block "
            "structure; it does not identify Q with a Waleffe triad operator."
        ),
        "Q_scalar_trace": float(scalar_trace),
        "Q_scalar_fro_norm": float(total_fro),
        "Q_helical_channel_block_fro_norms": {
            label: float(block_fro[label]) for label in ("++", "+-", "-+", "--")
        },
        "Q_helical_block_offdiag_to_total_fro_ratio": (
            float(off_fro / total_fro) if total_fro > 1.0e-14 else None
        ),
        "Q_helical_block_diag_to_total_fro_ratio": (
            float(diag_fro / total_fro) if total_fro > 1.0e-14 else None
        ),
        "Q_helical_channel_gram_symmetry_defect_fro": {
            label: float(math.sqrt(max(value, 0.0))) for label, value in gram_symmetry_defect.items()
        },
        "waleffe_helical_basis_relevant_observed": relevance_observed,
        "q_helical_block_diagonalization_observed": approx_block_diag,
        "rayleigh_on_known_vectors": rayleigh_on_vectors,
    }


def _q_helical_coupling_certificate_diagnostics(
    *,
    M_CC: np.ndarray,
    correction: np.ndarray,
    mode_keys: list[tuple[int, int, int]],
    max_dense_dim: int,
    matvec_backend: str = "cpu",
    gpu_checks: int = 2,
    tol: float = 1.0e-10,
) -> dict[str, Any]:
    """Exact dense candidate certificate for Q = D + E in helical channels.

    This is intentionally guarded: the lifted operator is 2n by 2n, so large
    shells must use checkpointed or future matrix-free/GPU overlays rather than
    blind dense allocation.
    """
    n = int(M_CC.shape[0])
    if n <= 1:
        return {
            "audit_requested": True,
            "status": "trivial",
            "candidate_certificate_only": True,
            "gpu_kn_authority": False,
        }
    if n > int(max_dense_dim):
        return {
            "audit_requested": True,
            "status": "skipped_oom_guard",
            "candidate_certificate_only": True,
            "gpu_kn_authority": False,
            "C_dimension": n,
            "lifted_dimension": 2 * n,
            "max_dense_dim": int(max_dense_dim),
            "recommended_path": (
                "write one shell-scoped Schur checkpoint, then rerun this overlay "
                "with a larger explicit guard or a future matrix-free/GPU parity path"
            ),
        }

    S_C = np.asarray(M_CC - correction, dtype=np.float64)
    _, _, q_scalar = _signed_split_from_schur(S_C)
    q_scalar = np.asarray(0.5 * (q_scalar + q_scalar.T), dtype=np.float64)
    h_plus, h_minus = _canonical_helical_frames(mode_keys)

    g_pp = np.real(h_plus.conj() @ h_plus.T)
    g_pm = np.real(h_plus.conj() @ h_minus.T)
    g_mp = np.real(h_minus.conj() @ h_plus.T)
    g_mm = np.real(h_minus.conj() @ h_minus.T)

    q_pp = np.asarray(q_scalar * g_pp, dtype=np.float64)
    q_pm = np.asarray(q_scalar * g_pm, dtype=np.float64)
    q_mp = np.asarray(q_scalar * g_mp, dtype=np.float64)
    q_mm = np.asarray(q_scalar * g_mm, dtype=np.float64)

    zero = np.zeros_like(q_scalar)
    D = np.block([[q_pp, zero], [zero, q_mm]])
    E = np.block([[zero, q_pm], [q_mp, zero]])
    Q = D + E
    D = np.asarray(0.5 * (D + D.T), dtype=np.float64)
    E = np.asarray(0.5 * (E + E.T), dtype=np.float64)
    Q = np.asarray(0.5 * (Q + Q.T), dtype=np.float64)

    gpu_schur_matvec_installed = False
    gpu_cpu_parity_observed = False
    gpu_helical_coupling_scout = False
    gpu_backend_status = "not_requested"
    gpu_backend_name = None
    gpu_vulkan_icd = None
    gpu_icd_probe_errors: list[dict[str, Any]] = []
    gpu_matvec_max_abs_error_good = None
    gpu_matvec_max_abs_error_bad = None

    if matvec_backend == "vulkan-scout":
        gpu_schur_matvec_installed = bool(
            create_vulkan_triad_laplacian_executor is not None and has_vulkan_triad_laplacian()
        )
        if gpu_schur_matvec_installed:
            try:
                total = np.asarray(M_CC - correction, dtype=np.float64)
                weights_good = np.maximum(-total, 0.0)
                weights_bad = np.maximum(total, 0.0)
                np.fill_diagonal(weights_good, 0.0)
                np.fill_diagonal(weights_bad, 0.0)
                profile = profile_from_weight_matrices(
                    weights_good,
                    weights_bad,
                    profile_id="schur-helical-certificate",
                )
                executor, probe_info = create_vulkan_triad_laplacian_executor(profile)
                gpu_backend_name = "vulkan-scout"
                gpu_backend_status = "ok"
                gpu_vulkan_icd = probe_info.get("vulkan_icd")
                gpu_icd_probe_errors = probe_info.get("icd_probe_errors", [])

                rng = np.random.default_rng(24680)
                good_errors: list[float] = []
                bad_errors: list[float] = []
                for _ in range(max(int(gpu_checks), 0)):
                    probe = rng.standard_normal(n)
                    probe /= max(float(np.linalg.norm(probe)), 1.0e-300)
                    good_errors.append(float(np.max(np.abs(executor.matvec_abs(probe) - weights_good @ probe))))
                    bad_errors.append(float(np.max(np.abs(executor.matvec_neg(probe) - weights_bad @ probe))))
                gpu_matvec_max_abs_error_good = max(good_errors) if good_errors else None
                gpu_matvec_max_abs_error_bad = max(bad_errors) if bad_errors else None
                gpu_cpu_parity_observed = bool(
                    gpu_matvec_max_abs_error_good is not None
                    and gpu_matvec_max_abs_error_bad is not None
                    and gpu_matvec_max_abs_error_good <= 5.0e-5
                    and gpu_matvec_max_abs_error_bad <= 5.0e-5
                )
                gpu_helical_coupling_scout = gpu_cpu_parity_observed
                executor.close()
            except Exception as exc:  # noqa: BLE001
                gpu_backend_status = f"parity_probe_failed:{type(exc).__name__}"
        else:
            gpu_backend_name = "vulkan-scout"
            gpu_backend_status = "vulkan_triad_laplacian_unavailable"

    basis = _one_perp_basis(n)
    P = np.block(
        [
            [basis, np.zeros_like(basis)],
            [np.zeros_like(basis), basis],
        ]
    )
    D_r = P.T @ D @ P
    E_r = P.T @ E @ P
    Q_r = P.T @ Q @ P

    d_evals, d_vecs = eigh(0.5 * (D_r + D_r.T), driver="evd")
    q_evals = _sym_eigvals(Q_r)
    e_evals = _sym_eigvals(E_r)
    positive = d_evals > max(tol, 0.0)
    if not bool(np.all(positive)):
        relative_kappa = None
        perturbation_bound = None
        actual_bound_ratio = None
    else:
        inv_sqrt = (d_vecs * (1.0 / np.sqrt(d_evals))) @ d_vecs.T
        rel = inv_sqrt @ E_r @ inv_sqrt
        rel_evals = _sym_eigvals(rel)
        relative_kappa = float(np.max(np.abs(rel_evals))) if rel_evals.size else 0.0
        perturbation_bound = float((1.0 - relative_kappa) * d_evals[0])
        actual_bound_ratio = (
            float(q_evals[0] / perturbation_bound)
            if perturbation_bound is not None and abs(perturbation_bound) > 1.0e-300
            else None
        )

    block_fro = {
        "++": float(np.linalg.norm(q_pp, ord="fro")),
        "+-": float(np.linalg.norm(q_pm, ord="fro")),
        "-+": float(np.linalg.norm(q_mp, ord="fro")),
        "--": float(np.linalg.norm(q_mm, ord="fro")),
    }
    off_fro = math.sqrt(block_fro["+-"] ** 2 + block_fro["-+"] ** 2)
    total_fro = float(np.linalg.norm(Q, ord="fro"))
    dominant_sector_pair = max(
        (("+ -", block_fro["+-"]), ("- +", block_fro["-+"])),
        key=lambda item: item[1],
    )[0]

    return {
        "audit_requested": True,
        "status": "ok",
        "candidate_certificate_only": True,
        "gpu_kn_authority": False,
        "C_dimension": n,
        "lifted_dimension": 2 * n,
        "Q_decomposition": "Q_N = D_N + E_N; D_N is helical channel block diagonal",
        "D_lambda_min_one_perp": float(d_evals[0]) if d_evals.size else None,
        "Q_lambda_min_one_perp": float(q_evals[0]) if q_evals.size else None,
        "E_operator_norm_one_perp": float(np.max(np.abs(e_evals))) if e_evals.size else None,
        "relative_bound_kappa": relative_kappa,
        "relative_bound_below_one_observed": (
            bool(relative_kappa < 1.0) if relative_kappa is not None else False
        ),
        "perturbation_lower_bound": perturbation_bound,
        "actual_to_bound_ratio": actual_bound_ratio,
        "off_block_frobenius_ratio": (
            float(off_fro / total_fro) if total_fro > 1.0e-14 else None
        ),
        "dominant_E_sector_pair_by_frobenius": dominant_sector_pair,
        "gpuSchurMatvecInstalled": gpu_schur_matvec_installed,
        "gpuCpuParityObserved": gpu_cpu_parity_observed,
        "gpuHelicalCouplingScout": gpu_helical_coupling_scout,
        "gpuKnAuthority": False,
        "gpuBackendStatus": gpu_backend_status,
        "gpuBackendName": gpu_backend_name,
        "gpuVulkanIcd": gpu_vulkan_icd,
        "gpuIcdProbeErrors": gpu_icd_probe_errors,
        "gpuMatvecMaxAbsErrorGood": gpu_matvec_max_abs_error_good,
        "gpuMatvecMaxAbsErrorBad": gpu_matvec_max_abs_error_bad,
        "helical_coupling_uniformly_bounded": False,
        "helical_block_floor_uniformly_proved": False,
        "gate1_conditional_theorem_proved": False,
    }


def _audit_row_from_checkpoint(
    *,
    checkpoint_path: Path,
    audit_q_helical_lift: bool = False,
    audit_q_helical_coupling_certificate: bool = False,
    helical_coupling_max_dense_dim: int = 2048,
    q_helical_matvec_backend: str = "cpu",
    gpu_matvec_checks: int = 2,
    domination_row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    domination_tol: float = 1.0e-8,
) -> dict[str, Any]:
    cached = _load_schur_checkpoint(checkpoint_path)
    result = dict(cached["result"])
    n = int(cached["N"])
    print(f"\n{'='*60}")
    print(f"  N={n}, K={cached['K']} (checkpoint overlay)")
    print(f"{'='*60}")
    print(
        "  Loaded checkpoint: "
        f"C size={cached['M_CC'].shape[0]}, "
        f"rho cached={((result.get('domination_ratio_matrix_free_diagnostics') or {}).get('domination_ratio_sup_one_perp'))}"
    )

    if audit_q_helical_lift:
        print("  Q helical-lift audit: candidate Waleffe channel lens...", end=" ", flush=True)
        result["Q_helical_lift_diagnostics"] = _q_helical_lift_diagnostics(
            M_CC=cached["M_CC"],
            correction=cached["correction"],
            shell_levels=cached["c_shell_levels"],
            mode_keys=cached["c_mode_keys"],
            rho_vec=cached["rho_vec"],
            q_bottom_vec=cached["q_bottom_vec"],
            row_chunk=domination_row_chunk,
            tol=domination_tol,
        )
        print("done.")
        if (result.get("Q_helical_lift_diagnostics") or {}).get("status") == "ok":
            print(
                "  Q helical lift offdiag/total="
                f"{result['Q_helical_lift_diagnostics']['Q_helical_block_offdiag_to_total_fro_ratio']}, "
                "blockdiag="
                f"{result['Q_helical_lift_diagnostics']['q_helical_block_diagonalization_observed']}"
            )

    if audit_q_helical_coupling_certificate:
        print("  Q helical coupling certificate: D+E relative-bound audit...", end=" ", flush=True)
        result["Q_helical_coupling_certificate_diagnostics"] = (
            _q_helical_coupling_certificate_diagnostics(
                M_CC=cached["M_CC"],
                correction=cached["correction"],
                mode_keys=cached["c_mode_keys"],
                max_dense_dim=helical_coupling_max_dense_dim,
                matvec_backend=q_helical_matvec_backend,
                gpu_checks=gpu_matvec_checks,
                tol=domination_tol,
            )
        )
        status = result["Q_helical_coupling_certificate_diagnostics"]["status"]
        print(f"{status}.")
        if status == "ok":
            diag = result["Q_helical_coupling_certificate_diagnostics"]
            print(
                "  Q helical coupling kappa="
                f"{diag['relative_bound_kappa']}, "
                "bound="
                f"{diag['perturbation_lower_bound']}"
            )

    result["checkpoint_overlay_used"] = True
    result["checkpoint_schema_version"] = cached["schema_version"]
    return result


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
    audit_effective_laplacian_signs: bool = False,
    audit_signed_factorization: bool = False,
    audit_domination_ratio_matrix_free: bool = False,
    domination_row_chunk: int = DEFAULT_DOMINATION_CHUNK_SIZE,
    domination_eps: float = DEFAULT_DOMINATION_EPS,
    domination_tol: float = 1.0e-8,
    domination_maxiter: int = 200,
    audit_domination_symmetry_sectors: bool = False,
    audit_extremizer_angular_frame: bool = False,
    audit_domination_restricted_sector: bool = False,
    audit_domination_halo_growth: bool = False,
    audit_domination_coarse_quotient: bool = False,
    audit_domination_row_pairing: bool = False,
    audit_q_helical_lift: bool = False,
    audit_q_helical_coupling_certificate: bool = False,
    helical_coupling_max_dense_dim: int = 2048,
    q_helical_matvec_backend: str = "cpu",
    domination_restricted_nonaxis_only: bool = True,
    domination_restricted_orbit_labels: list[str] | None = None,
    domination_restricted_matvec_backend: str = "cpu",
    gpu_matvec_checks: int = 2,
    domination_halo_support_tol: float = 1.0e-12,
    domination_halo_max_radius: int = 6,
    domination_halo_rho_match_factor: float = 1.02,
    domination_halo_overlap_target: float = 0.90,
    domination_halo_boundary_flux_target: float = 0.05,
    domination_coarse_quotient_scheme: str = "shell-zero-orbit",
    write_schur_checkpoint: Path | None = None,
    partial_json_path: Path | None = None,
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
    c_mode_keys = _c_block_mode_keys(bundle, snapshot, n, c_indices, zero_eps)
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
    row_sum_diag: dict[str, Any] | None = None
    sign_audit_diag: dict[str, Any] | None = None
    signed_factorization_diag: dict[str, Any] | None = None
    domination_ratio_diag: dict[str, Any] | None = None
    domination_restricted_diag: dict[str, Any] | None = None
    domination_halo_diag: dict[str, Any] | None = None
    domination_coarse_quotient_diag: dict[str, Any] | None = None
    domination_row_pairing_diag: dict[str, Any] | None = None
    q_helical_lift_diag: dict[str, Any] | None = None
    q_helical_coupling_diag: dict[str, Any] | None = None

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
        row_sum_diag = _schur_row_sum_diagnostics(M_CC, M_GC, M_GG_chol)
        naive_bound = (gc_norm ** 2) / max(stats_gg["lambda_min"], 1.0e-300)
        print(f"  ‖M_CG M_GG⁻¹ M_GC‖ = {correction_norm:.6e}  (naive bound: {naive_bound:.6e})")
        print(f"  max |S_C 1_C| = {row_sum_diag['max_abs_row_sum']:.6e}")

        if nc <= dense_schur_threshold:
            # Dense eigh path — exact, used for N≤10
            print(f"  Computing S_C (dense eigh, n={nc})...", end=" ", flush=True)
            S_C_dense = M_CC - correction
            stats_sc = _block_stats("S_C", S_C_dense)
            if audit_effective_laplacian_signs:
                sign_audit_diag = _effective_laplacian_sign_diagnostics(
                    S_C_dense, row_sum_diag
                )
            if audit_signed_factorization:
                signed_factorization_diag = _signed_factorization_diagnostics(S_C_dense)
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
            if audit_domination_ratio_matrix_free:
                print(
                    "  Computing domination ratio "
                    f"(projected generalized eig, n={nc})...",
                    end=" ",
                    flush=True,
                )
                domination_ratio_diag = _domination_ratio_matrix_free_diagnostics(
                    M_CC,
                    correction,
                    shell_levels=c_shell_levels,
                    mode_keys=c_mode_keys,
                    row_chunk=domination_row_chunk,
                    eps=domination_eps,
                    tol=domination_tol,
                    maxiter=domination_maxiter,
                    audit_symmetry_sectors=audit_domination_symmetry_sectors,
                    audit_angular_frame=audit_extremizer_angular_frame,
                )
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
                if audit_domination_ratio_matrix_free:
                    print(
                        "  Computing domination ratio "
                        f"(matrix-free generalized eig, n={nc})...",
                        end=" ",
                        flush=True,
                    )
                    domination_ratio_diag = _domination_ratio_matrix_free_diagnostics(
                        M_CC,
                        correction,
                        shell_levels=c_shell_levels,
                        mode_keys=c_mode_keys,
                        row_chunk=domination_row_chunk,
                        eps=domination_eps,
                        tol=domination_tol,
                        maxiter=domination_maxiter,
                        audit_symmetry_sectors=audit_domination_symmetry_sectors,
                        audit_angular_frame=audit_extremizer_angular_frame,
                    )
                    print("done.")
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
        if row_sum_diag is not None:
            print(f"  Row-sum residual: max={row_sum_diag['max_abs_row_sum']:.6e}, "
                  f"L2={row_sum_diag['l2_row_sum']:.6e}")
    if audit_effective_laplacian_signs:
        if sign_audit_diag is not None:
            print(
                "  Effective-sign audit: "
                f"positive_offdiag={sign_audit_diag['num_positive_offdiag']}, "
                f"neg_components={sign_audit_diag['negative_edge_support_components']}, "
                f"route={sign_audit_diag['route_verdict']}"
            )
        else:
            sign_audit_diag = {
                "audit_requested": True,
                "dense_audit_available": False,
                "route_verdict": "signed_psd_required",
            }
    if audit_signed_factorization:
        if signed_factorization_diag is not None:
            print(
                "  Signed-factorization audit: "
                f"rho_sup={signed_factorization_diag['domination_ratio_sup_one_perp']}, "
                f"lambda1_good={signed_factorization_diag['L_good_lambda1']}, "
                f"domination={signed_factorization_diag['domination_holds_strictly_observed']}"
            )
        else:
            signed_factorization_diag = {
                "audit_requested": True,
                "dense_audit_available": False,
            }
    if audit_domination_ratio_matrix_free:
        if domination_ratio_diag is not None:
            print(
                "  Matrix-free domination audit: "
                f"rho_sup={domination_ratio_diag['domination_ratio_sup_one_perp']}, "
                f"lambda1_good={domination_ratio_diag['L_good_lambda1_one_perp']}, "
                f"lambda_max_bad={domination_ratio_diag['L_bad_lambda_max_one_perp']}"
            )
        else:
            domination_ratio_diag = {
                "audit_requested": True,
                "dense_audit_available": False,
                "matrix_free_requested": True,
                "status": "unavailable",
            }
    if audit_domination_restricted_sector:
        if sc_ok and domination_ratio_diag is not None and correction_norm is not None:
            print(
                "  Restricted-sector domination audit: "
                f"backend={domination_restricted_matvec_backend}...",
                end=" ",
                flush=True,
            )
            domination_restricted_diag = _domination_ratio_restricted_sector_diagnostics(
                n=n,
                M_CC=M_CC,
                correction=correction,
                shell_levels=c_shell_levels,
                mode_keys=c_mode_keys,
                full_diag=domination_ratio_diag,
                row_chunk=domination_row_chunk,
                eps=domination_eps,
                tol=domination_tol,
                maxiter=domination_maxiter,
                nonaxis_only=domination_restricted_nonaxis_only,
                orbit_labels=domination_restricted_orbit_labels,
                matvec_backend=domination_restricted_matvec_backend,
                gpu_checks=gpu_matvec_checks,
            )
            print("done.")
            if domination_restricted_diag.get("status") == "ok":
                print(
                    "  Restricted-sector rho_sup="
                    f"{domination_restricted_diag['domination_ratio_sup_one_perp']}, "
                    "full overlap="
                    f"{(domination_restricted_diag.get('full_comparison') or {}).get('full_extremizer_sector_projected_overlap')}"
                )
        if domination_restricted_diag is None:
            domination_restricted_diag = {
                "audit_requested": True,
                "status": "unavailable",
                "gpu_kn_authority": False,
            }
    if audit_domination_halo_growth:
        if sc_ok and domination_ratio_diag is not None and correction_norm is not None:
            print(
                "  Halo-growth domination audit: "
                f"backend={domination_restricted_matvec_backend}...",
                end=" ",
                flush=True,
            )
            domination_halo_diag = _domination_halo_growth_diagnostics(
                n=n,
                M_CC=M_CC,
                correction=correction,
                shell_levels=c_shell_levels,
                mode_keys=c_mode_keys,
                full_diag=domination_ratio_diag,
                row_chunk=domination_row_chunk,
                eps=domination_eps,
                tol=domination_tol,
                maxiter=domination_maxiter,
                nonaxis_only=domination_restricted_nonaxis_only,
                orbit_labels=domination_restricted_orbit_labels,
                matvec_backend=domination_restricted_matvec_backend,
                gpu_checks=gpu_matvec_checks,
                support_tol=domination_halo_support_tol,
                max_radius=domination_halo_max_radius,
                rho_match_factor=domination_halo_rho_match_factor,
                overlap_target=domination_halo_overlap_target,
                boundary_flux_target=domination_halo_boundary_flux_target,
            )
            print("done.")
            best_radius = domination_halo_diag.get("best_radius") or {}
            if best_radius:
                print(
                    "  Halo-growth best radius="
                    f"{best_radius.get('radius')}, "
                    f"rho/full={best_radius.get('rho_ratio_to_full')}, "
                    f"overlap={best_radius.get('full_extremizer_sector_projected_overlap')}, "
                    f"boundary={best_radius.get('boundary_flux_ratio')}"
                )
        if domination_halo_diag is None:
            domination_halo_diag = {
                "audit_requested": True,
                "status": "unavailable",
                "gpu_kn_authority": False,
            }
    if audit_domination_coarse_quotient:
        if sc_ok and domination_ratio_diag is not None and correction_norm is not None:
            print(
                "  Coarse-quotient domination audit: "
                f"scheme={domination_coarse_quotient_scheme}...",
                end=" ",
                flush=True,
            )
            domination_coarse_quotient_diag = _domination_coarse_quotient_diagnostics(
                n=n,
                M_CC=M_CC,
                correction=correction,
                shell_levels=c_shell_levels,
                mode_keys=c_mode_keys,
                full_diag=domination_ratio_diag,
                nonaxis_only=domination_restricted_nonaxis_only,
                scheme=domination_coarse_quotient_scheme,
            )
            print("done.")
            if domination_coarse_quotient_diag.get("status") == "ok":
                full_cmp = domination_coarse_quotient_diag.get("full_comparison") or {}
                print(
                    "  Coarse quotient rho_sup="
                    f"{domination_coarse_quotient_diag['quotient_domination_ratio_sup_one_perp']}, "
                    "rho/full="
                    f"{full_cmp.get('rho_ratio_to_full')}, "
                    "overlap="
                    f"{full_cmp.get('full_extremizer_projected_overlap')}"
                )
        if domination_coarse_quotient_diag is None:
            domination_coarse_quotient_diag = {
                "audit_requested": True,
                "status": "unavailable",
                "gpu_kn_authority": False,
            }
    if audit_domination_row_pairing:
        if sc_ok and correction_norm is not None:
            print("  Row-pairing audit: Q = 2L_good - 3L_bad...", end=" ", flush=True)
            domination_row_pairing_diag = _domination_row_pairing_diagnostics(
                M_CC=M_CC,
                correction=correction,
                shell_levels=c_shell_levels,
                mode_keys=c_mode_keys,
                full_diag=domination_ratio_diag,
                row_chunk=domination_row_chunk,
                tol=domination_tol,
                maxiter=domination_maxiter,
            )
            print("done.")
            if domination_row_pairing_diag.get("status") == "ok":
                print(
                    "  Row-pairing max(3bad/2good)="
                    f"{domination_row_pairing_diag['max_row_3bad_2good_ratio']}, "
                    "lambda_min(Q|1^⊥)="
                    f"{domination_row_pairing_diag['Q_lambda_min_one_perp']}"
                )
        if domination_row_pairing_diag is None:
            domination_row_pairing_diag = {
                "audit_requested": True,
                "status": "unavailable",
                "gpu_kn_authority": False,
            }

    base_result = {
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
        "row_sum_diagnostics": row_sum_diag,
        "effective_laplacian_sign_diagnostics": sign_audit_diag,
        "signed_factorization_diagnostics": signed_factorization_diag,
        "domination_ratio_matrix_free_diagnostics": domination_ratio_diag,
        "domination_ratio_restricted_sector_diagnostics": domination_restricted_diag,
        "domination_halo_growth_diagnostics": domination_halo_diag,
        "domination_coarse_quotient_diagnostics": domination_coarse_quotient_diag,
        "domination_row_pairing_diagnostics": domination_row_pairing_diag,
        "Q_helical_lift_diagnostics": None,
        "Q_helical_coupling_certificate_diagnostics": None,
        "schur_complement_ok": sc_ok,
        "verdict": verdict,
        "c0": C0,
        "candidate_only": True,
        "theorem_promoted": False,
    }
    if partial_json_path is not None:
        _write_partial_row_receipt(partial_json_path, base_result)
        print(f"  Partial receipt → {partial_json_path}")
    if write_schur_checkpoint is not None and sc_ok and correction_norm is not None:
        core_path, matrices_path = _write_schur_checkpoint(
            base_path=write_schur_checkpoint,
            n=n,
            cutoff=cutoff,
            M_CC=M_CC,
            correction=correction,
            c_shell_levels=c_shell_levels,
            c_mode_keys=c_mode_keys,
            result=base_result,
        )
        print(f"  Checkpoint core → {core_path}")
        print(f"  Checkpoint mats → {matrices_path}")

    if audit_q_helical_lift:
        if sc_ok and correction_norm is not None:
            print("  Q helical-lift audit: candidate Waleffe channel lens...", end=" ", flush=True)
            q_helical_lift_diag = _q_helical_lift_diagnostics(
                M_CC=M_CC,
                correction=correction,
                shell_levels=c_shell_levels,
                mode_keys=c_mode_keys,
                rho_vec=(
                    np.asarray((domination_ratio_diag or {}).get("_rho_vec_full", []), dtype=np.float64)
                    if domination_ratio_diag is not None
                    else None
                ),
                q_bottom_vec=(
                    np.asarray((domination_row_pairing_diag or {}).get("_q_bottom_vec_full", []), dtype=np.float64)
                    if domination_row_pairing_diag is not None
                    else None
                ),
                row_chunk=domination_row_chunk,
                tol=domination_tol,
            )
            print("done.")
            if q_helical_lift_diag.get("status") == "ok":
                print(
                    "  Q helical lift offdiag/total="
                    f"{q_helical_lift_diag['Q_helical_block_offdiag_to_total_fro_ratio']}, "
                    "blockdiag="
                    f"{q_helical_lift_diag['q_helical_block_diagonalization_observed']}"
                )
        if q_helical_lift_diag is None:
            q_helical_lift_diag = {
                "audit_requested": True,
                "status": "unavailable",
                "gpu_kn_authority": False,
            }

    if audit_q_helical_coupling_certificate:
        if sc_ok and correction_norm is not None:
            print("  Q helical coupling certificate: D+E relative-bound audit...", end=" ", flush=True)
            q_helical_coupling_diag = _q_helical_coupling_certificate_diagnostics(
                M_CC=M_CC,
                correction=correction,
                mode_keys=c_mode_keys,
                max_dense_dim=helical_coupling_max_dense_dim,
                matvec_backend=q_helical_matvec_backend,
                gpu_checks=gpu_matvec_checks,
                tol=domination_tol,
            )
            print(f"{q_helical_coupling_diag.get('status')}.")
            if q_helical_coupling_diag.get("status") == "ok":
                print(
                    "  Q helical coupling kappa="
                    f"{q_helical_coupling_diag['relative_bound_kappa']}, "
                    "bound="
                    f"{q_helical_coupling_diag['perturbation_lower_bound']}"
                )
        if q_helical_coupling_diag is None:
            q_helical_coupling_diag = {
                "audit_requested": True,
                "status": "unavailable",
                "gpu_kn_authority": False,
            }

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
        "row_sum_diagnostics": row_sum_diag,
        "effective_laplacian_sign_diagnostics": sign_audit_diag,
        "signed_factorization_diagnostics": signed_factorization_diag,
        "domination_ratio_matrix_free_diagnostics": domination_ratio_diag,
        "domination_ratio_restricted_sector_diagnostics": domination_restricted_diag,
        "domination_halo_growth_diagnostics": domination_halo_diag,
        "domination_coarse_quotient_diagnostics": domination_coarse_quotient_diag,
        "domination_row_pairing_diagnostics": domination_row_pairing_diag,
        "Q_helical_lift_diagnostics": q_helical_lift_diag,
        "Q_helical_coupling_certificate_diagnostics": q_helical_coupling_diag,
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
        "| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \\|S_C 1\\| | corr(constant) | Verdict |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|",
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
        corr_constant = nvd.get("corr_constant")
        corr_constant_str = (
            f"{corr_constant:.4f}"
            if corr_constant is not None and not (isinstance(corr_constant, float) and math.isnan(corr_constant))
            else "—"
        )
        row_sum = (r.get("row_sum_diagnostics") or {}).get("max_abs_row_sum")
        row_sum_str = f"{row_sum:.2e}" if row_sum is not None else "—"
        lines.append(
            f"| {r['N']} | {r['block_size']} | {r['G_size']} | {r['C_size']} | "
            f"{r['M_CC']['lambda_min']:.6e} | {eig_strs[0]} | {eig_strs[1]} | {eig_strs[2]} | "
            f"{sc_nullity} | {row_sum_str} | {corr_constant_str} | {r['verdict']} |"
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
        row_sum_diag = r.get("row_sum_diagnostics") or {}
        if row_sum_diag:
            lines.append(
                f"N={r['N']}: max |S_C 1_C|={row_sum_diag['max_abs_row_sum']:.6e}, "
                f"L2 row-sum residual={row_sum_diag['l2_row_sum']:.6e}"
            )
        sign_diag = r.get("effective_laplacian_sign_diagnostics") or {}
        if sign_diag.get("dense_audit_available"):
            lines.append(
                f"N={r['N']}: sign audit positive_offdiag={sign_diag['num_positive_offdiag']}, "
                f"negative-edge components={sign_diag['negative_edge_support_components']}, "
                f"route={sign_diag['route_verdict']}"
            )
        factor_diag = r.get("signed_factorization_diagnostics") or {}
        if factor_diag.get("dense_audit_available"):
            lines.append(
                f"N={r['N']}: signed-factorization rho_sup={factor_diag['domination_ratio_sup_one_perp']:.6e}, "
                f"lambda1(L_good)={factor_diag['L_good_lambda1']:.6e}, "
                f"domination={factor_diag['domination_holds_strictly_observed']}"
            )
        mf_diag = r.get("domination_ratio_matrix_free_diagnostics") or {}
        if mf_diag.get("status") == "ok":
            lines.append(
                f"N={r['N']}: matrix-free rho_sup={mf_diag['domination_ratio_sup_one_perp']:.6e}, "
                f"lambda1(L_good)={mf_diag['L_good_lambda1_one_perp']:.6e}, "
                f"lambda_max(L_bad)={mf_diag['L_bad_lambda_max_one_perp']:.6e}, "
                f"resid={mf_diag['domination_ratio_residual_norm']:.2e}"
            )
        rest_diag = r.get("domination_ratio_restricted_sector_diagnostics") or {}
        if rest_diag.get("status") == "ok":
            full_cmp = rest_diag.get("full_comparison") or {}
            lines.append(
                f"N={r['N']}: restricted rho_sup={rest_diag['domination_ratio_sup_one_perp']:.6e}, "
                f"sector_dim={rest_diag['sector_dimension']}, "
                f"rho/full={full_cmp.get('rho_ratio_to_full')}, "
                f"overlap={full_cmp.get('full_extremizer_sector_projected_overlap')}, "
                f"backend={rest_diag.get('matvec_backend')}"
            )
        halo_diag = r.get("domination_halo_growth_diagnostics") or {}
        if halo_diag.get("status") == "ok":
            best_radius = halo_diag.get("best_radius") or {}
            if best_radius:
                lines.append(
                    f"N={r['N']}: halo best radius={best_radius.get('radius')}, "
                    f"sector_dim={best_radius.get('sector_dimension')}, "
                    f"rho/full={best_radius.get('rho_ratio_to_full')}, "
                    f"overlap={best_radius.get('full_extremizer_sector_projected_overlap')}, "
                    f"boundary={best_radius.get('boundary_flux_ratio')}"
                )
            else:
                last_row = (halo_diag.get("radii") or [])[-1] if halo_diag.get("radii") else {}
                lines.append(
                    f"N={r['N']}: halo no stop radius within max_radius={halo_diag.get('max_radius')}, "
                    f"last_dim={last_row.get('sector_dimension')}, "
                    f"last_rho/full={last_row.get('rho_ratio_to_full')}, "
                    f"last_overlap={last_row.get('full_extremizer_sector_projected_overlap')}"
                )
        quotient_diag = r.get("domination_coarse_quotient_diagnostics") or {}
        if quotient_diag.get("status") == "ok":
            full_cmp = quotient_diag.get("full_comparison") or {}
            lines.append(
                f"N={r['N']}: coarse quotient rho_sup={quotient_diag['quotient_domination_ratio_sup_one_perp']:.6e}, "
                f"class_count={quotient_diag.get('class_count')}, "
                f"rho/full={full_cmp.get('rho_ratio_to_full')}, "
                f"overlap={full_cmp.get('full_extremizer_projected_overlap')}"
            )
        row_pair_diag = r.get("domination_row_pairing_diagnostics") or {}
        if row_pair_diag.get("status") == "ok":
            q_sign = row_pair_diag.get("Q_sign_diagnostics") or {}
            lines.append(
                f"N={r['N']}: row-pairing max(3bad/2good)={row_pair_diag['max_row_3bad_2good_ratio']:.6e}, "
                f"lambda_min(Q|1^⊥)={row_pair_diag['Q_lambda_min_one_perp']:.6e}, "
                f"Q positive_offdiag={q_sign.get('num_positive_offdiag')}, "
                f"Q Gershgorin lower={q_sign.get('gershgorin_lower_bound'):.6e}"
            )
        helical_diag = r.get("Q_helical_lift_diagnostics") or {}
        if helical_diag.get("status") == "ok":
            lines.append(
                f"N={r['N']}: Q helical-lift offdiag/total="
                f"{helical_diag['Q_helical_block_offdiag_to_total_fro_ratio']:.6e}, "
                f"basis_relevant={helical_diag['waleffe_helical_basis_relevant_observed']}, "
                f"blockdiag={helical_diag['q_helical_block_diagonalization_observed']}"
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
    parser.add_argument(
        "--audit-effective-laplacian-signs",
        action="store_true",
        help=(
            "For dense S_C shells, audit whether the Schur complement is an ordinary "
            "graph Laplacian shortcut (nonpositive off-diagonals + connected negative-edge support) "
            "or whether the signed-PSD route is still required."
        ),
    )
    parser.add_argument(
        "--audit-signed-factorization",
        action="store_true",
        help=(
            "For dense S_C shells, decompose S_C = L_good - L_bad and report the "
            "observed domination ratio sup_{x ⟂ 1} x^T L_bad x / x^T L_good x."
        ),
    )
    parser.add_argument(
        "--audit-domination-ratio-matrix-free",
        action="store_true",
        help=(
            "Compute the projected generalized domination ratio on 1_C^⊥ using "
            "CPU matrix-free chunked Laplacian matvecs derived from the Schur block."
        ),
    )
    parser.add_argument(
        "--domination-row-chunk",
        type=int,
        default=DEFAULT_DOMINATION_CHUNK_SIZE,
        help="Row chunk size for the CPU matrix-free domination-ratio matvecs.",
    )
    parser.add_argument(
        "--domination-eps",
        type=float,
        default=DEFAULT_DOMINATION_EPS,
        help="Regularization epsilon added to L_good on 1_C^⊥ inside the generalized solver.",
    )
    parser.add_argument(
        "--domination-tol",
        type=float,
        default=1.0e-8,
        help="LOBPCG tolerance for the domination-ratio projected generalized eigensolve.",
    )
    parser.add_argument(
        "--domination-maxiter",
        type=int,
        default=200,
        help="LOBPCG max iterations for the domination-ratio projected generalized eigensolve.",
    )
    parser.add_argument(
        "--audit-domination-symmetry-sectors",
        action="store_true",
        help=(
            "Augment the matrix-free domination audit with symmetry-sector anatomy "
            "for the observed extremizer: coordinate-permutation orbit, zero-count, "
            "sign-parity, shell class, and axis/non-axis restricted Rayleigh quotients."
        ),
    )
    parser.add_argument(
        "--audit-extremizer-angular-frame",
        action="store_true",
        help=(
            "Augment the matrix-free domination audit with top-mode angular/frame "
            "diagnostics for the observed extremizer: pairwise normalized wavevector "
            "dot products, mass near -1/2, 0, +1/2, and weighted frame spectra."
        ),
    )
    parser.add_argument(
        "--audit-domination-restricted-sector",
        action="store_true",
        help=(
            "Compute the generalized domination ratio on a candidate restricted sector: "
            "non-axis seam modes supported on selected coordinate-permutation orbits."
        ),
    )
    parser.add_argument(
        "--audit-domination-halo-growth",
        action="store_true",
        help=(
            "Grow a restricted sector outward from the seed orbit layer by Schur-support adjacency "
            "and report the first halo radius whose restricted generalized domination solve matches "
            "the full extremizer within the requested tolerances."
        ),
    )
    parser.add_argument(
        "--audit-domination-coarse-quotient",
        action="store_true",
        help=(
            "Compress the non-axis seam into a coarse class-indicator quotient and solve "
            "the projected generalized domination problem on that quotient."
        ),
    )
    parser.add_argument(
        "--audit-domination-row-pairing",
        action="store_true",
        help=(
            "Audit the row-level pairing route through Q = 2L_good - 3L_bad: "
            "row bad/good ratios, Q sign structure, Gershgorin margins, and "
            "the bottom spectrum of Q on 1_C^⊥."
        ),
    )
    parser.add_argument(
        "--audit-q-helical-lift",
        action="store_true",
        help=(
            "Build a candidate canonical helical-channel lift of Q = 2L_good - 3L_bad "
            "and measure whether the current phase-based Q shows approximate Waleffe-style "
            "channel block structure. Observational only; not a theorem lane."
        ),
    )
    parser.add_argument(
        "--audit-q-helical-coupling-certificate",
        action="store_true",
        help=(
            "Build the candidate lifted helical decomposition Q_N = D_N + E_N and "
            "compute the dense relative bound ||D^-1/2 E D^-1/2||. "
            "Guarded by --helical-coupling-max-dense-dim to avoid OOM."
        ),
    )
    parser.add_argument(
        "--helical-coupling-max-dense-dim",
        type=int,
        default=2048,
        help=(
            "Maximum seam C dimension for the exact dense helical D+E certificate. "
            "Larger shells return skipped_oom_guard unless this is raised explicitly."
        ),
    )
    parser.add_argument(
        "--q-helical-matvec-backend",
        choices=("cpu", "torch-gpu-scout", "vulkan-scout"),
        default="cpu",
        help=(
            "Optional parity backend for the helical Schur split. "
            "The dense certificate remains CPU-authored; the backend is scout-only."
        ),
    )
    parser.add_argument(
        "--domination-restricted-orbit-label",
        action="append",
        default=None,
        help=(
            "Orbit label to include in the restricted sector, for example '(0,1,N-1)' after "
            "instantiating N. May be repeated. Defaults to the candidate orbit layer."
        ),
    )
    parser.add_argument(
        "--domination-restricted-allow-axis",
        action="store_true",
        help="Include axis modes in the restricted-sector audit. Default keeps the sector non-axis only.",
    )
    parser.add_argument(
        "--domination-restricted-matvec-backend",
        choices=("cpu", "torch-gpu-scout", "vulkan-scout"),
        default="cpu",
        help=(
            "Matvec backend for the restricted-sector generalized solve. "
            "'torch-gpu-scout' and 'vulkan-scout' are non-authoritative and fall back to CPU if unavailable or parity fails."
        ),
    )
    parser.add_argument(
        "--gpu-matvec-checks",
        type=int,
        default=2,
        help="Parity probes for the restricted-sector torch GPU scout backend before CPU fallback.",
    )
    parser.add_argument(
        "--domination-halo-support-tol",
        type=float,
        default=1.0e-12,
        help="Absolute Schur-entry threshold for halo-growth support adjacency.",
    )
    parser.add_argument(
        "--domination-halo-max-radius",
        type=int,
        default=6,
        help="Maximum Schur-support halo radius to test around the seed sector.",
    )
    parser.add_argument(
        "--domination-halo-rho-match-factor",
        type=float,
        default=1.02,
        help="Stop criterion target for rho_sector / rho_full.",
    )
    parser.add_argument(
        "--domination-halo-overlap-target",
        type=float,
        default=0.90,
        help="Stop criterion target for overlap with the projected full extremizer.",
    )
    parser.add_argument(
        "--domination-halo-boundary-flux-target",
        type=float,
        default=0.05,
        help="Stop criterion target for boundary flux ratio of the full extremizer.",
    )
    parser.add_argument(
        "--domination-coarse-quotient-scheme",
        choices=("shell-orbit", "shell-zero-orbit", "shell-zero-orbit-parity", "shell-zero"),
        default="shell-zero-orbit",
        help="Class-label compression scheme for the coarse quotient domination audit.",
    )
    parser.add_argument(
        "--write-schur-checkpoint",
        type=Path,
        default=None,
        help=(
            "Write a shell-scoped Schur/Q checkpoint after the expensive solve. "
            "Writes sibling '.core.npz' and '.matrices.npz' files."
        ),
    )
    parser.add_argument(
        "--read-schur-checkpoint",
        type=Path,
        default=None,
        help=(
            "Read a shell-scoped Schur/Q checkpoint and reuse cached M_CC/correction/"
            "vectors for overlay diagnostics instead of recomputing the full audit."
        ),
    )
    args = parser.parse_args()

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    results = []
    if args.read_schur_checkpoint is not None:
        if any(
            flag
            for flag in (
                args.audit_effective_laplacian_signs,
                args.audit_signed_factorization,
                args.audit_domination_restricted_sector,
                args.audit_domination_halo_growth,
                args.audit_domination_coarse_quotient,
                args.audit_domination_row_pairing,
            )
        ):
            raise SystemExit(
                "--read-schur-checkpoint currently supports cached-row replay plus "
                "--audit-q-helical-lift/--audit-q-helical-coupling-certificate overlays; "
                "rerun the full audit for other diagnostics."
            )
        results.append(
            _audit_row_from_checkpoint(
                checkpoint_path=args.read_schur_checkpoint,
                audit_q_helical_lift=args.audit_q_helical_lift,
                audit_q_helical_coupling_certificate=args.audit_q_helical_coupling_certificate,
                helical_coupling_max_dense_dim=args.helical_coupling_max_dense_dim,
                q_helical_matvec_backend=args.q_helical_matvec_backend,
                domination_row_chunk=args.domination_row_chunk,
                domination_tol=args.domination_tol,
            )
        )
    else:
        bundle = _load_raw_bundle(Path(args.raw_archive), [])
        snapped = _frame_indices(bundle.frame_count, frame=None, frame_limit=1)
        snapshot = int(snapped[0][1] if isinstance(snapped[0], tuple) else snapped[0])

        for n in sorted(args.shells):
            cutoff = n - 1
            builder = args.profile_builder
            effective_full_domination = bool(
                args.audit_domination_ratio_matrix_free
                or args.audit_domination_restricted_sector
                or args.audit_domination_halo_growth
                or args.audit_domination_coarse_quotient
                or args.audit_domination_row_pairing
                or args.audit_q_helical_lift
                or args.audit_q_helical_coupling_certificate
            )
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
                audit_effective_laplacian_signs=args.audit_effective_laplacian_signs,
                audit_signed_factorization=args.audit_signed_factorization,
                audit_domination_ratio_matrix_free=effective_full_domination,
                domination_row_chunk=args.domination_row_chunk,
                domination_eps=args.domination_eps,
                domination_tol=args.domination_tol,
                domination_maxiter=args.domination_maxiter,
                audit_domination_symmetry_sectors=args.audit_domination_symmetry_sectors,
                audit_extremizer_angular_frame=args.audit_extremizer_angular_frame,
                audit_domination_restricted_sector=args.audit_domination_restricted_sector,
                audit_domination_halo_growth=args.audit_domination_halo_growth,
                audit_domination_coarse_quotient=args.audit_domination_coarse_quotient,
                audit_domination_row_pairing=args.audit_domination_row_pairing,
                audit_q_helical_lift=args.audit_q_helical_lift,
                audit_q_helical_coupling_certificate=args.audit_q_helical_coupling_certificate,
                helical_coupling_max_dense_dim=args.helical_coupling_max_dense_dim,
                q_helical_matvec_backend=args.q_helical_matvec_backend,
                domination_restricted_nonaxis_only=not args.domination_restricted_allow_axis,
                domination_restricted_orbit_labels=args.domination_restricted_orbit_label,
                domination_restricted_matvec_backend=args.domination_restricted_matvec_backend,
                gpu_matvec_checks=args.gpu_matvec_checks,
                domination_halo_support_tol=args.domination_halo_support_tol,
                domination_halo_max_radius=args.domination_halo_max_radius,
                domination_halo_rho_match_factor=args.domination_halo_rho_match_factor,
                domination_halo_overlap_target=args.domination_halo_overlap_target,
                domination_halo_boundary_flux_target=args.domination_halo_boundary_flux_target,
                domination_coarse_quotient_scheme=args.domination_coarse_quotient_scheme,
                write_schur_checkpoint=(
                    _row_checkpoint_base_path(args.write_schur_checkpoint, n)
                    if args.write_schur_checkpoint is not None
                    else None
                ),
                partial_json_path=_row_partial_json_path(output_dir / "schur_audit.partial.json", n),
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
    dense_domination_rows = [
        r for r in results
        if (r.get("signed_factorization_diagnostics") or {}).get("dense_audit_available")
    ]
    domination_ratio_below_one_observed = bool(dense_domination_rows) and all(
        (r["signed_factorization_diagnostics"] or {}).get("domination_holds_strictly_observed") is True
        for r in dense_domination_rows
    )
    matrix_free_domination_rows = [
        r for r in results
        if (r.get("domination_ratio_matrix_free_diagnostics") or {}).get("status") == "ok"
    ]
    if matrix_free_domination_rows:
        domination_ratio_below_one_observed = domination_ratio_below_one_observed or all(
            (r["domination_ratio_matrix_free_diagnostics"] or {}).get("domination_holds_strictly_observed") is True
            for r in matrix_free_domination_rows
        )
    restricted_rows = [
        r for r in results
        if (r.get("domination_ratio_restricted_sector_diagnostics") or {}).get("status") == "ok"
    ]
    halo_rows = [
        r for r in results
        if (r.get("domination_halo_growth_diagnostics") or {}).get("status") == "ok"
    ]
    quotient_rows = [
        r for r in results
        if (r.get("domination_coarse_quotient_diagnostics") or {}).get("status") == "ok"
    ]
    row_pair_rows = [
        r for r in results
        if (r.get("domination_row_pairing_diagnostics") or {}).get("status") == "ok"
    ]
    q_helical_rows = [
        r for r in results
        if (r.get("Q_helical_lift_diagnostics") or {}).get("status") == "ok"
    ]
    q_helical_coupling_rows = [
        r for r in results
        if (r.get("Q_helical_coupling_certificate_diagnostics") or {}).get("status") == "ok"
    ]
    gpu_restricted_rows = [
        r for r in restricted_rows
        if (r.get("domination_ratio_restricted_sector_diagnostics") or {}).get("gpu_domination_scout_installed")
    ]
    gpu_restricted_parity_rows = [
        r for r in gpu_restricted_rows
        if (r.get("domination_ratio_restricted_sector_diagnostics") or {}).get("gpu_cpu_parity_observed") is True
    ]

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
        "gate1_target": (
            "Uniform signed domination on 1_C^⊥: "
            "sup_x⊥1_C (x^T L_bad x)/(x^T L_good x) ≤ rho_* < 1"
        ),
        "schurNullModeIsConstantProved": True,
        "kronStyleSchurReductionIdentified": True,
        "ordinaryKronLaplacianIdentified": False,
        "ordinaryKronLaplacianRoute": False,
        "balancedSignedGraphRoute": False,
        "effectiveOffdiagNonpositiveProved": False,
        "effectiveGraphConnectedProved": False,
        "effectiveGraphConnectedObserved": bool(
            any(
                (r.get("effective_laplacian_sign_diagnostics") or {}).get("dense_audit_available")
                for r in results
            )
            and all(
                (r.get("effective_laplacian_sign_diagnostics") or {}).get("negative_edge_support_components") == 1
                for r in results
                if (r.get("effective_laplacian_sign_diagnostics") or {}).get("dense_audit_available")
            )
        ),
        "schurComplementPsdVerified": bool(psd_verified),
        "schurComplementNullityOneObserved": bool(nullity_one_observed),
        "schurSignedPsdRequired": bool(
            any(
                (r.get("effective_laplacian_sign_diagnostics") or {}).get("route_verdict") == "signed_psd_required"
                for r in results
            )
        ),
        "signedDominationProbeInstalled": bool(
            any(
                r.get("signed_factorization_diagnostics") is not None
                or r.get("domination_ratio_matrix_free_diagnostics") is not None
                for r in results
            )
        ),
        "signedDominationRatioBelowOneObserved": domination_ratio_below_one_observed,
        "signedDominationRatioUniformlyBounded": False,
        "restrictedSectorDominationAuditInstalled": bool(restricted_rows),
        "haloGrowthDominationAuditInstalled": bool(halo_rows),
        "coarseQuotientDominationAuditInstalled": bool(quotient_rows),
        "rowPairingDominationAuditInstalled": bool(row_pair_rows),
        "qHelicalLiftAuditInstalled": bool(q_helical_rows),
        "qHelicalCouplingCertificateAuditInstalled": bool(q_helical_coupling_rows),
        "gpuDominationScoutInstalled": bool(gpu_restricted_rows),
        "gpuDominationScoutMatchesCpu": (
            bool(
                gpu_restricted_rows
                and all(
                    (r["domination_ratio_restricted_sector_diagnostics"] or {}).get("gpu_domination_scout_matches_cpu")
                    is True
                    for r in gpu_restricted_rows
                )
            )
            if gpu_restricted_rows
            else False
        ),
        "gpuSchurMatvecInstalled": bool(
            q_helical_coupling_rows
            and all(
                (r.get("Q_helical_coupling_certificate_diagnostics") or {}).get("gpuSchurMatvecInstalled")
                is True
                for r in q_helical_coupling_rows
            )
        ),
        "gpuCpuParityObserved": bool(
            gpu_restricted_parity_rows
            or (
                q_helical_coupling_rows
                and all(
                    (r.get("Q_helical_coupling_certificate_diagnostics") or {}).get("gpuCpuParityObserved")
                    is True
                    for r in q_helical_coupling_rows
                )
            )
        ),
        "gpuHelicalCouplingScout": bool(
            q_helical_coupling_rows
            and all(
                (r.get("Q_helical_coupling_certificate_diagnostics") or {}).get("gpuHelicalCouplingScout")
                is True
                for r in q_helical_coupling_rows
            )
        ),
        "gpuKnAuthority": False,
        "waleffeHelicalBasisRelevantObserved": bool(
            q_helical_rows
            and all(
                (r.get("Q_helical_lift_diagnostics") or {}).get("waleffe_helical_basis_relevant_observed")
                is True
                for r in q_helical_rows
            )
        ),
        "qHelicalBlockDiagonalizationObserved": bool(
            q_helical_rows
            and all(
                (r.get("Q_helical_lift_diagnostics") or {}).get("q_helical_block_diagonalization_observed")
                is True
                for r in q_helical_rows
            )
        ),
        "qHelicalCouplingBoundObserved": bool(
            q_helical_coupling_rows
            and all(
                (r.get("Q_helical_coupling_certificate_diagnostics") or {}).get(
                    "relative_bound_below_one_observed"
                )
                is True
                for r in q_helical_coupling_rows
            )
        ),
        "qHelicalMatvecBackend": (
            q_helical_coupling_rows[0]["Q_helical_coupling_certificate_diagnostics"].get("gpuBackendName")
            if q_helical_coupling_rows
            else None
        ),
        "qHelicalCouplingUniformlyBounded": False,
        "qHelicalBlockFloorUniformlyProved": False,
        "qHelicalSectorPsdProved": False,
        "qEqualsWaleffeTriadOperatorProved": False,
        "qGlobalPsdProved": False,
        "schurComplementMatrixFreeAuditInstalled": True,
        "schurNullModeConstantOnCObserved": bool(
            all(
                (r.get("null_vector_diagnostics") or {}).get("corr_constant") is not None
                and abs((r["null_vector_diagnostics"] or {})["corr_constant"]) >= 0.999
                for r in results
                if r.get("null_vector_diagnostics") is not None
            )
        ),
        "schurComplementPsdProved": False,
        "schurNullModeIdentified": False,
        "schurSignedFactorizationProved": False,
        "schurNullModeFactorizationProved": False,
        "gate1ConditionalTheoremProved": False,
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
