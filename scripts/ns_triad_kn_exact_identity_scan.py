#!/usr/bin/env python3
"""Audit the corrected K_N exact-identity route on the active NS Wall 1 carrier.

This scan replaces the broken signed full-space route with the positive-subspace
identity built from the existing negative-frame / absolute-frame decomposition:

    L_abs   = B^T W_abs B
    L_neg   = B^T W_neg B
    L_signed = L_abs - 2 L_neg
    K_N     = L_abs^{-1/2} L_neg L_abs^{-1/2}

On im(L_abs), the corrected identity is

    L_signed_norm = L_abs^{-1/2} L_signed L_abs^{-1/2} = I - 2 K_N.

The surface is fail-closed and candidate-only. It does not promote any theorem,
full-NS, or Clay status.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    ERROR_STATUS,
    OK_STATUS,
    PARTIAL_STATUS,
    _build_frame_surface,
    _collect_modes,
    _family_laplacians,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_triad_cocycle_floor_scan import _mode_shell_filter, _validate_shells  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_exact_identity_scan.py"
CONTRACT = "ns_triad_kn_exact_identity_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EXACT_IDENTITY_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_exact_identity_scan_N128_20260623.json"
)
DEFAULT_SHELLS = (2, 3)

CONTROL_CARD = {
    "O": "Measure the corrected K_N exact-identity route on the active NS Wall 1 shell carrier.",
    "R": (
        "Build L_abs, L_neg, and K_N from the existing frame-family split, restrict to im(L_abs), "
        "and audit the corrected identity L_signed_norm = I - 2 K_N together with negative-frame coverage."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; exact-identity and frame-coercivity metrics are empirical and non-promoting.",
    "L": (
        "Load raw frames, select shell carriers, build the frame surface, assemble L_abs/L_neg/L_signed, "
        "restrict to the positive subspace, audit the exact identity, and summarize spectral support."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this scan.",
    "F": (
        "The scan audits the corrected positive-subspace identity and frame-support proxies only; "
        "it does not prove uniform coercivity or equidistribution."
    ),
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
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


def _laplacian(adjacency: np.ndarray) -> np.ndarray:
    if adjacency.size == 0:
        return np.zeros_like(adjacency, dtype=np.float64)
    degree = np.sum(adjacency, axis=1)
    lap = np.diag(degree) - adjacency
    return 0.5 * (lap + lap.T)


def _incidence_matrix(triads: list[Any], mode_count: int) -> np.ndarray:
    incidence = np.zeros((len(triads), mode_count), dtype=np.float64)
    for row_index, triad in enumerate(triads):
        incidence[row_index, int(triad.left)] = 1.0
        incidence[row_index, int(triad.right)] = 1.0
        incidence[row_index, int(triad.out)] = -1.0
    return incidence


def _positive_subspace(matrix: np.ndarray, tol: float) -> tuple[np.ndarray, np.ndarray]:
    evals, evecs = np.linalg.eigh(0.5 * (matrix + matrix.T))
    mask = np.asarray(evals > tol, dtype=bool)
    return np.asarray(evals[mask], dtype=np.float64), np.asarray(evecs[:, mask], dtype=np.float64)


def _sqrt_pinv_from_positive_subspace(evals: np.ndarray, basis: np.ndarray) -> np.ndarray:
    if basis.size == 0 or len(evals) == 0:
        return np.zeros((basis.shape[0] if basis.ndim == 2 else 0, basis.shape[0] if basis.ndim == 2 else 0), dtype=np.float64)
    scales = np.asarray([1.0 / math.sqrt(float(value)) for value in evals], dtype=np.float64)
    return (basis * scales) @ basis.T


def _safe_rank(matrix: np.ndarray, tol: float) -> int:
    if matrix.size == 0:
        return 0
    return int(np.linalg.matrix_rank(matrix, tol=tol))


def _pearson(a: np.ndarray, b: np.ndarray) -> float:
    if len(a) == 0 or len(b) == 0 or len(a) != len(b):
        return 0.0
    if np.allclose(a, a[0]) or np.allclose(b, b[0]):
        return 0.0
    corr = np.corrcoef(a, b)[0, 1]
    return float(corr) if math.isfinite(float(corr)) else 0.0


def _row(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    shell_n: int,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "shell": int(shell_n),
        "top_k": int(top_k),
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        modes = _collect_modes(
            spectrum,
            top_k=int(top_k),
            zero_eps=float(zero_eps),
            pool_multiplier=int(pool_multiplier),
        )
        shell_modes = _mode_shell_filter(modes, shell_n)
        triads, frame_metrics = _build_frame_surface(shell_modes, zero_eps=zero_eps, triad_sample_limit=8)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"kn_exact_identity_scan_error: {exc}"]
        return ERROR_STATUS, row

    mode_count = int(len(shell_modes))
    triad_count = int(len(triads))
    row["selected_mode_count"] = mode_count
    row["triad_count"] = triad_count

    if mode_count < 2 or triad_count == 0:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_insufficient_modes"]
        return PARTIAL_STATUS, row

    positive_adj, negative_adj, _combined_adj = _family_laplacians(triads, mode_count)
    abs_adj = positive_adj + negative_adj
    l_abs = _laplacian(abs_adj)
    l_neg = _laplacian(negative_adj)
    l_signed = l_abs - 2.0 * l_neg

    tol = max(float(zero_eps), 1.0e-10)
    pos_evals, pos_basis = _positive_subspace(l_abs, tol=tol)
    positive_rank = int(len(pos_evals))
    if positive_rank == 0:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["l_abs_has_no_positive_subspace"]
        return PARTIAL_STATUS, row

    l_abs_inv_sqrt = _sqrt_pinv_from_positive_subspace(pos_evals, pos_basis)
    k_matrix = 0.5 * (l_abs_inv_sqrt @ l_neg @ l_abs_inv_sqrt + (l_abs_inv_sqrt @ l_neg @ l_abs_inv_sqrt).T)
    signed_norm = 0.5 * (
        l_abs_inv_sqrt @ l_signed @ l_abs_inv_sqrt + (l_abs_inv_sqrt @ l_signed @ l_abs_inv_sqrt).T
    )

    k_reduced = 0.5 * (pos_basis.T @ k_matrix @ pos_basis + (pos_basis.T @ k_matrix @ pos_basis).T)
    signed_reduced = 0.5 * (pos_basis.T @ signed_norm @ pos_basis + (pos_basis.T @ signed_norm @ pos_basis).T)
    identity_reduced = np.eye(positive_rank, dtype=np.float64) - 2.0 * k_reduced

    residual = signed_reduced - identity_reduced
    residual_op = float(np.linalg.norm(residual, ord=2))
    residual_fro = float(np.linalg.norm(residual, ord="fro"))

    k_eigs = np.linalg.eigvalsh(k_reduced) if positive_rank > 0 else np.zeros(0, dtype=np.float64)
    signed_eigs = np.linalg.eigvalsh(signed_reduced) if positive_rank > 0 else np.zeros(0, dtype=np.float64)

    negative_triads = [triad for triad in triads if float(triad.coherence) < 0.0]
    all_incidence = _incidence_matrix(triads, mode_count)
    neg_incidence = _incidence_matrix(negative_triads, mode_count)
    rank_all = _safe_rank(all_incidence, tol=tol)
    rank_neg = _safe_rank(neg_incidence, tol=tol)
    spanning_match = bool(rank_all > 0 and rank_neg == rank_all)

    sign_bits = np.asarray([1.0 if float(triad.coherence) < 0.0 else 0.0 for triad in triads], dtype=np.float64)
    log_weights = np.asarray(
        [math.log(max(float(triad.weight), tol)) for triad in triads],
        dtype=np.float64,
    )
    sign_magnitude_corr = abs(_pearson(sign_bits, log_weights))

    row.update(
        {
            "l_abs_positive_rank": positive_rank,
            "l_abs_trace": float(np.trace(l_abs)),
            "l_neg_trace": float(np.trace(l_neg)),
            "l_signed_trace": float(np.trace(l_signed)),
            "exact_identity_residual_op": residual_op,
            "exact_identity_residual_fro": residual_fro,
            "lambda_min_kn": float(np.min(k_eigs)) if len(k_eigs) else 0.0,
            "lambda_max_kn": float(np.max(k_eigs)) if len(k_eigs) else 0.0,
            "lambda_min_signed_norm": float(np.min(signed_eigs)) if len(signed_eigs) else 0.0,
            "lambda_max_signed_norm": float(np.max(signed_eigs)) if len(signed_eigs) else 0.0,
            "negative_triads_count": int(len(negative_triads)),
            "negative_sign_fraction": float(np.mean(sign_bits)) if len(sign_bits) else 0.0,
            "negative_frame_mass_ratio": float(frame_metrics.get("triad_negative_frame_mass_ratio", 0.0)),
            "negative_sign_magnitude_correlation_abs": float(sign_magnitude_corr),
            "rank_b": rank_all,
            "rank_b_neg": rank_neg,
            "negative_spanning_matches_total_rank": spanning_match,
            "negative_spanning_coverage_fraction": float(rank_neg / max(rank_all, 1)),
            "wall1_floor_lower_bound_from_kn": float(np.min(k_eigs)) if len(k_eigs) else 0.0,
            "wall1_frame_safety_margin_from_kn": float(1.0 - np.max(k_eigs)) if len(k_eigs) else 0.0,
        }
    )
    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    metric_rows = [row for row in rows if row.get("status") in {OK_STATUS, PARTIAL_STATUS}]

    def mean(key: str) -> float:
        values = [float(row[key]) for row in metric_rows if isinstance(row.get(key), (int, float))]
        return float(sum(values) / len(values)) if values else 0.0

    def maximum(key: str) -> float:
        values = [float(row[key]) for row in metric_rows if isinstance(row.get(key), (int, float))]
        return float(max(values)) if values else 0.0

    rank_matches = [1.0 if row.get("negative_spanning_matches_total_rank") else 0.0 for row in metric_rows]
    return {
        "shared_frame_shell_count": int(len(metric_rows)),
        "lambda_min_kn_mean": mean("lambda_min_kn"),
        "lambda_min_kn_min": min((float(row["lambda_min_kn"]) for row in metric_rows if isinstance(row.get("lambda_min_kn"), (int, float))), default=0.0),
        "lambda_max_kn_mean": mean("lambda_max_kn"),
        "wall1_floor_lower_bound_from_kn_mean": mean("wall1_floor_lower_bound_from_kn"),
        "wall1_frame_safety_margin_from_kn_mean": mean("wall1_frame_safety_margin_from_kn"),
        "exact_identity_residual_op_mean": mean("exact_identity_residual_op"),
        "exact_identity_residual_op_max": maximum("exact_identity_residual_op"),
        "exact_identity_residual_fro_mean": mean("exact_identity_residual_fro"),
        "exact_identity_residual_fro_max": maximum("exact_identity_residual_fro"),
        "negative_sign_fraction_mean": mean("negative_sign_fraction"),
        "negative_frame_mass_ratio_mean": mean("negative_frame_mass_ratio"),
        "negative_sign_magnitude_correlation_abs_mean": mean("negative_sign_magnitude_correlation_abs"),
        "negative_spanning_match_fraction": float(sum(rank_matches) / len(rank_matches)) if rank_matches else 0.0,
        "negative_spanning_coverage_fraction_mean": mean("negative_spanning_coverage_fraction"),
        "kn_exact_identity_status": "fail-closed",
        "wall1a_status": "unproved",
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells)
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    rows: list[dict[str, Any]] = []
    errors: list[str] = []
    statuses: list[str] = []

    for snapshot in _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit):
        for shell_n in shells:
            status, row = _row(
                slot=snapshot,
                snapshot=snapshot,
                bundle=bundle,
                top_k=args.top_k,
                pool_multiplier=args.pool_multiplier,
                zero_eps=args.zero_eps,
                shell_n=shell_n,
            )
            statuses.append(status)
            if status == ERROR_STATUS:
                errors.extend(row.get("errors", []))
            rows.append(row)

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
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "shells": [int(shell) for shell in shells],
        },
        "status": ERROR_STATUS if any(status == ERROR_STATUS for status in statuses) else (PARTIAL_STATUS if any(status == PARTIAL_STATUS for status in statuses) else OK_STATUS),
        "rows": rows,
        "aggregate": _aggregate_rows(rows),
        "warnings": warnings,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0 if payload["status"] != ERROR_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
