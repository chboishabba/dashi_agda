#!/usr/bin/env python3
"""Audit directional Schur-complement gap proxies on the active NS Wall 1 shell carrier."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    OK_STATUS,
    PARTIAL_STATUS,
    ERROR_STATUS,
    _build_frame_surface,
    _collect_modes,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _mode_strata,
    _scalar_vorticity_spectrum,
)
from ns_triad_cocycle_floor_scan import _mode_shell_filter, _validate_shells  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_schur_directional_audit_scan.py"
CONTRACT = "ns_triad_schur_directional_audit_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SCHUR_DIRECTIONAL_AUDIT_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_schur_directional_audit_scan_N128_20260622.json"
)

CONTROL_CARD = {
    "O": "Measure directional Schur-complement gap proxies on the active NS Wall 1 shell carrier.",
    "R": (
        "Split the carrier into low/high shell blocks, build a normalized negative-frame operator K, "
        "and audit directional q_diag - q_coup gaps for the dangerous shell."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; Schur gaps are empirical and non-promoting.",
    "L": (
        "Load raw frames, select dominant modes, build the frame surface, form K, partition it into shell blocks, "
        "and emit Schur directional gap proxies."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this scan.",
    "F": "The scan estimates Schur directional gaps only; it does not prove a uniform frame gap.",
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


def _family_adjacencies(triads: list[Any], mode_count: int) -> tuple[np.ndarray, np.ndarray]:
    positive = np.zeros((mode_count, mode_count), dtype=np.float64)
    negative = np.zeros((mode_count, mode_count), dtype=np.float64)
    for triad in triads:
        pair_weight = float(triad.weight) / 3.0
        pos_weight = pair_weight * max(float(triad.coherence), 0.0)
        neg_weight = pair_weight * max(-float(triad.coherence), 0.0)
        for left, right in ((triad.left, triad.right), (triad.left, triad.out), (triad.right, triad.out)):
            positive[left, right] += pos_weight
            positive[right, left] += pos_weight
            negative[left, right] += neg_weight
            negative[right, left] += neg_weight
    return positive, negative


def _laplacian(adjacency: np.ndarray) -> np.ndarray:
    degree = np.sum(adjacency, axis=1)
    return np.diag(degree) - adjacency


def _matrix_sqrt_pinv(matrix: np.ndarray, tol: float) -> np.ndarray:
    evals, evecs = np.linalg.eigh(matrix)
    scales = np.asarray([1.0 / math.sqrt(float(v)) if float(v) > float(tol) else 0.0 for v in evals], dtype=np.float64)
    return (evecs * scales) @ evecs.T


def _operator_k(positive_adj: np.ndarray, negative_adj: np.ndarray, zero_eps: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    l_pos = _laplacian(positive_adj) + np.eye(positive_adj.shape[0], dtype=np.float64) * float(max(zero_eps, 1.0e-9))
    l_neg = _laplacian(negative_adj)
    l_pos_inv_sqrt = _matrix_sqrt_pinv(l_pos, tol=max(float(zero_eps), 1.0e-12))
    k = l_pos_inv_sqrt @ l_neg @ l_pos_inv_sqrt
    k = 0.5 * (k + k.T)
    return k, l_pos, l_neg


def _partition_indices(shell_radii: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    labels, stratum_count, _ = _mode_strata(shell_radii)
    if stratum_count <= 1:
        index = np.arange(len(shell_radii), dtype=np.int64)
        return index, np.zeros(0, dtype=np.int64)
    low = np.where(labels == np.min(labels))[0]
    high = np.where(labels == np.max(labels))[0]
    return np.asarray(low, dtype=np.int64), np.asarray(high, dtype=np.int64)


def _schur_metrics(k: np.ndarray, low: np.ndarray, high: np.ndarray, zero_eps: float) -> dict[str, float]:
    if len(low) == 0 or len(high) == 0:
        return {
            "k00_lambda_max": 0.0,
            "k11_lambda_max": 0.0,
            "k01_operator_norm": 0.0,
            "schur_min_eigenvalue": 0.0,
            "schur_directional_gap_min": 0.0,
            "schur_directional_gap_mean": 0.0,
            "dangerous_subspace_weight_fraction": 0.0,
        }
    k00 = k[np.ix_(low, low)]
    k11 = k[np.ix_(high, high)]
    k01 = k[np.ix_(low, high)]
    k10 = k01.T
    id00 = np.eye(k00.shape[0], dtype=np.float64)
    id11 = np.eye(k11.shape[0], dtype=np.float64)
    reg = max(float(zero_eps), 1.0e-9)
    i_minus_k00 = id00 - k00 + reg * id00
    i_minus_k11 = id11 - k11
    inv00 = np.linalg.pinv(i_minus_k00, rcond=max(float(zero_eps), 1.0e-10))
    schur = i_minus_k11 - k10 @ inv00 @ k01
    schur = 0.5 * (schur + schur.T)
    k00_eigs = np.linalg.eigvalsh(k00) if k00.size else np.zeros(0, dtype=np.float64)
    k11_eigs = np.linalg.eigvalsh(k11) if k11.size else np.zeros(0, dtype=np.float64)
    schur_eigs = np.linalg.eigvalsh(schur) if schur.size else np.zeros(0, dtype=np.float64)
    top_evals, top_evecs = np.linalg.eigh(k11)
    order = np.argsort(top_evals)[::-1]
    directional_gaps: list[float] = []
    total_top_mass = float(np.sum(np.maximum(top_evals, 0.0)))
    dangerous_weight = float(np.max(np.maximum(top_evals, 0.0))) if len(top_evals) else 0.0
    for idx in order[: min(3, len(order))]:
        u = top_evecs[:, idx]
        q_diag = float(u.T @ i_minus_k11 @ u)
        q_coup = float(u.T @ k10 @ inv00 @ k01 @ u)
        directional_gaps.append(float(q_diag - q_coup))
    return {
        "k00_lambda_max": float(np.max(k00_eigs)) if len(k00_eigs) else 0.0,
        "k11_lambda_max": float(np.max(k11_eigs)) if len(k11_eigs) else 0.0,
        "k01_operator_norm": float(np.linalg.norm(k01, ord=2)) if k01.size else 0.0,
        "schur_min_eigenvalue": float(np.min(schur_eigs)) if len(schur_eigs) else 0.0,
        "schur_directional_gap_min": float(np.min(directional_gaps)) if directional_gaps else 0.0,
        "schur_directional_gap_mean": float(np.mean(directional_gaps)) if directional_gaps else 0.0,
        "dangerous_subspace_weight_fraction": float(dangerous_weight / max(total_top_mass, float(zero_eps))) if len(top_evals) else 0.0,
    }


def _invalid_schur_surface(schur_metrics: dict[str, float], zero_eps: float) -> bool:
    tol = max(float(zero_eps), 1.0e-9)
    for key in (
        "k00_lambda_max",
        "k11_lambda_max",
        "k01_operator_norm",
        "schur_min_eigenvalue",
        "schur_directional_gap_min",
        "schur_directional_gap_mean",
        "dangerous_subspace_weight_fraction",
    ):
        value = schur_metrics.get(key)
        if not isinstance(value, (int, float)) or not math.isfinite(float(value)):
            return True
    if float(schur_metrics["k00_lambda_max"]) < -tol or float(schur_metrics["k11_lambda_max"]) < -tol:
        return True
    if float(schur_metrics["k00_lambda_max"]) > 1.0 + tol or float(schur_metrics["k11_lambda_max"]) > 1.0 + tol:
        return True
    if float(schur_metrics["dangerous_subspace_weight_fraction"]) < -tol:
        return True
    if float(schur_metrics["dangerous_subspace_weight_fraction"]) > 1.0 + tol:
        return True
    return False


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
        "top_k": int(top_k),
        "shell": int(shell_n),
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
        triads, metrics = _build_frame_surface(shell_modes, zero_eps=zero_eps, triad_sample_limit=8)
        shell_radii = np.asarray([mode.shell_radius for mode in shell_modes], dtype=np.float64)
        low, high = _partition_indices(shell_radii)
        positive_adj, negative_adj = _family_adjacencies(triads, len(shell_modes))
        k, _l_pos, _l_neg = _operator_k(positive_adj, negative_adj, zero_eps=zero_eps)
        schur_metrics = _schur_metrics(k, low, high, zero_eps=zero_eps)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_schur_directional_audit_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(len(shell_modes)),
            "triad_count": int(metrics["triad_count"]),
            "carrier_stratum_count": int(metrics["carrier_stratum_count"]),
            "frame_stability_margin_proxy": float(metrics["frame_stability_margin_proxy"]),
            "positive_backbone_operator_gap_proxy": float(metrics["positive_backbone_operator_gap_proxy"]),
            "negative_frame_operator_gap_proxy": float(metrics["negative_frame_operator_gap_proxy"]),
            "low_block_size": int(len(low)),
            "high_block_size": int(len(high)),
        }
    )

    row["raw_k00_lambda_max"] = float(schur_metrics["k00_lambda_max"])
    row["raw_k11_lambda_max"] = float(schur_metrics["k11_lambda_max"])
    row["raw_k01_operator_norm"] = float(schur_metrics["k01_operator_norm"])
    row["raw_schur_min_eigenvalue"] = float(schur_metrics["schur_min_eigenvalue"])
    row["raw_schur_directional_gap_min"] = float(schur_metrics["schur_directional_gap_min"])
    row["raw_schur_directional_gap_mean"] = float(schur_metrics["schur_directional_gap_mean"])
    row["raw_dangerous_subspace_weight_fraction"] = float(schur_metrics["dangerous_subspace_weight_fraction"])

    warnings: list[str] = []
    invalid_surface = _invalid_schur_surface(schur_metrics, zero_eps=zero_eps)

    if invalid_surface:
        row.update(
            {
                "k00_lambda_max": None,
                "k11_lambda_max": None,
                "k01_operator_norm": None,
                "schur_min_eigenvalue": None,
                "schur_directional_gap_min": None,
                "schur_directional_gap_mean": None,
                "schur_directional_gap_proxy": None,
                "schur_directional_gap_lower_bound": None,
                "schur_directional_gap_residual": None,
                "schur_directional_gap_ratio": None,
                "dangerous_subspace_weight_fraction": None,
            }
        )
        warnings.append("schur surface left admissible operator regime; downgraded to unavailable")
    else:
        row.update(
            {
                "k00_lambda_max": float(schur_metrics["k00_lambda_max"]),
                "k11_lambda_max": float(schur_metrics["k11_lambda_max"]),
                "k01_operator_norm": float(schur_metrics["k01_operator_norm"]),
                "schur_min_eigenvalue": float(schur_metrics["schur_min_eigenvalue"]),
                "schur_directional_gap_min": float(schur_metrics["schur_directional_gap_min"]),
                "schur_directional_gap_mean": float(schur_metrics["schur_directional_gap_mean"]),
                "schur_directional_gap_proxy": float(schur_metrics["schur_directional_gap_min"]),
                "schur_directional_gap_lower_bound": float(schur_metrics["schur_min_eigenvalue"]),
                "schur_directional_gap_residual": float(
                    schur_metrics["schur_directional_gap_mean"] - schur_metrics["schur_directional_gap_min"]
                ),
                "schur_directional_gap_ratio": float(
                    schur_metrics["schur_directional_gap_min"]
                    / max(1.0 - schur_metrics["k11_lambda_max"], float(zero_eps))
                ),
                "dangerous_subspace_weight_fraction": float(schur_metrics["dangerous_subspace_weight_fraction"]),
            }
        )

    if int(metrics["triad_count"]) <= 0:
        warnings.append("no resonant triads in selected carrier")
    if len(high) == 0:
        warnings.append("dangerous shell block collapsed")
    if not invalid_surface and float(schur_metrics["k01_operator_norm"]) <= 0.0:
        warnings.append("cross-shell coupling collapsed to zero")
    if warnings:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = warnings
        return PARTIAL_STATUS, row

    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            value = row.get(key)
            if isinstance(value, (int, float)) and math.isfinite(float(value)):
                values.append(float(value))
        return values

    return {
        "processed_frames": int(len(rows)),
        "ok_frames": int(sum(1 for row in rows if row.get("status") == OK_STATUS)),
        "partial_frames": int(sum(1 for row in rows if row.get("status") == PARTIAL_STATUS)),
        "error_frames": int(sum(1 for row in rows if row.get("status") == ERROR_STATUS)),
        "k00_lambda_max_mean": float(np.mean(_series("k00_lambda_max"))) if _series("k00_lambda_max") else None,
        "k11_lambda_max_mean": float(np.mean(_series("k11_lambda_max"))) if _series("k11_lambda_max") else None,
        "k01_operator_norm_mean": float(np.mean(_series("k01_operator_norm"))) if _series("k01_operator_norm") else None,
        "schur_min_eigenvalue_mean": float(np.mean(_series("schur_min_eigenvalue"))) if _series("schur_min_eigenvalue") else None,
        "schur_directional_gap_min_mean": float(np.mean(_series("schur_directional_gap_min"))) if _series("schur_directional_gap_min") else None,
        "schur_directional_gap_mean_mean": float(np.mean(_series("schur_directional_gap_mean"))) if _series("schur_directional_gap_mean") else None,
        "dangerous_subspace_weight_fraction_mean": float(np.mean(_series("dangerous_subspace_weight_fraction")))
        if _series("dangerous_subspace_weight_fraction")
        else None,
        "schur_gap_vs_cross_shell_correlation": _pearson(
            _series("schur_directional_gap_min"),
            _series("k01_operator_norm"),
        ),
        "schur_gap_vs_frame_margin_correlation": _pearson(
            _series("schur_directional_gap_min"),
            _series("frame_stability_margin_proxy"),
        ),
    }


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    shells = _validate_shells(args.shells)
    snapshots = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)
    rows: list[dict[str, Any]] = []
    for slot, snapshot in enumerate(snapshots):
        for shell_n in shells:
            _status, row = _row(
                slot=int(slot),
                snapshot=int(snapshot),
                bundle=bundle,
                top_k=int(args.top_k),
                pool_multiplier=int(args.pool_multiplier),
                zero_eps=float(args.zero_eps),
                shell_n=int(shell_n),
            )
            rows.append(row)

    payload = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "authority": AUTHORITY,
        "warnings": warnings,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "output_json": str(args.output_json),
        },
        "parameters": {
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "shells": [int(shell) for shell in shells],
        },
        "rows": rows,
        "aggregate": _aggregate(rows),
    }
    payload["status"] = OK_STATUS if not any(row.get("status") == ERROR_STATUS for row in rows) else PARTIAL_STATUS
    payload["ok"] = payload["status"] == OK_STATUS
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
