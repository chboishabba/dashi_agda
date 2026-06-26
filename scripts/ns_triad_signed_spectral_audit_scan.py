#!/usr/bin/env python3
"""Audit signed-Laplacian spectral surfaces for the active NS Wall 1 route."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
from ns_triad_cocycle_floor_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_SEED,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    ERROR_STATUS,
    OK_STATUS,
    PARTIAL_STATUS,
    _choose_best_reference,
    _collect_modes,
    _fit_phase_field,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _mode_arrays,
    _mode_shell_filter,
    _triadwise_oracle_target,
    _validate_shells,
    _wrap_phase,
)
from ns_low_frustration_basin_scan import _build_triad_links, _scalar_vorticity_spectrum  # type: ignore
from ns_triad_schur_directional_audit_scan import _operator_k  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_signed_spectral_audit_scan.py"
CONTRACT = "ns_triad_signed_spectral_audit_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_SPECTRAL_AUDIT_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_spectral_audit_scan_N128_20260622.json"
)
DEFAULT_SHELLS = (2, 3)

CONTROL_CARD = {
    "O": "Measure signed-Laplacian spectral telemetry on the active NS Wall 1 shell carrier.",
    "R": (
        "Build the signed shell operator, audit the candidate identity L_signed_norm = I - K, "
        "and separate lower spectral-edge frame risk from upper spectral-edge XY-floor risk."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; the signed spectral audit is empirical and non-promoting.",
    "L": (
        "Load raw frames, select shell carriers, build the oracle sign pattern, assemble signed adjacencies, "
        "derive normalized signed Laplacian and K, and emit endpoint-aware spectral metrics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this scan.",
    "F": "The scan audits spectral surfaces only; it does not prove a uniform signed-expander or Schur theorem.",
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
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _oracle_sign_bits(target_cocycle: np.ndarray) -> np.ndarray:
    bits = []
    for angle in np.asarray(target_cocycle, dtype=np.float64):
        wrapped = float(_wrap_phase(float(angle)))
        zero_dist = abs(wrapped)
        pi_dist = abs(_wrap_phase(wrapped - math.pi))
        bits.append(1 if pi_dist < zero_dist else 0)
    return np.asarray(bits, dtype=np.uint8)


def _pairwise_signed_adjacency(triads: list[Any], sign_bits: np.ndarray, mode_count: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    positive = np.zeros((mode_count, mode_count), dtype=np.float64)
    negative = np.zeros((mode_count, mode_count), dtype=np.float64)
    for edge_index, triad in enumerate(triads):
        pair_weight = float(triad.weight) / 3.0
        target = negative if int(sign_bits[edge_index]) == 1 else positive
        for left, right in ((int(triad.left), int(triad.right)), (int(triad.left), int(triad.out)), (int(triad.right), int(triad.out))):
            target[left, right] += pair_weight
            target[right, left] += pair_weight
    return positive, negative, positive - negative


def _normalized_signed_laplacian(signed_adjacency: np.ndarray, zero_eps: float) -> np.ndarray:
    abs_degree = np.sum(np.abs(signed_adjacency), axis=1)
    regularized = np.maximum(abs_degree, max(float(zero_eps), 1.0e-9))
    inv_sqrt = np.diag(1.0 / np.sqrt(regularized))
    identity = np.eye(signed_adjacency.shape[0], dtype=np.float64)
    lap = identity - inv_sqrt @ signed_adjacency @ inv_sqrt
    return 0.5 * (lap + lap.T)


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
        triad_links = _build_triad_links(shell_modes, zero_eps=float(zero_eps))
        amplitudes, phases, _, shell_coord = _mode_arrays(shell_modes)
        fitted_phase, _, _, _, _ = _fit_phase_field(shell_modes, zero_eps=zero_eps)
        _best_reference, _best_shift, reference_rows = _choose_best_reference(
            phases=phases,
            amplitudes=amplitudes,
            shell_coord=shell_coord,
            fitted_phase=fitted_phase,
            triad_links=triad_links,
            zero_eps=zero_eps,
        )
        oracle_target, oracle_metrics = _triadwise_oracle_target(reference_rows, len(triad_links))
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"signed_spectral_audit_scan_error: {exc}"]
        return ERROR_STATUS, row

    mode_count = int(len(shell_modes))
    triad_count = int(len(triad_links))
    row["selected_mode_count"] = mode_count
    row["triad_count"] = triad_count
    row["oracle_reference_unique_count"] = int(oracle_metrics["oracle_reference_unique_count"])
    if triad_count == 0 or mode_count < 2:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_insufficient_modes"]
        return PARTIAL_STATUS, row

    sign_bits = _oracle_sign_bits(oracle_target)
    positive_adj, negative_adj, signed_adj = _pairwise_signed_adjacency(triad_links, sign_bits, mode_count)
    l_signed_norm = _normalized_signed_laplacian(signed_adj, zero_eps=zero_eps)
    k_matrix, _, _ = _operator_k(positive_adj, negative_adj, zero_eps=zero_eps)
    identity_surface = np.eye(mode_count, dtype=np.float64) - k_matrix
    identity_error_fro = float(np.linalg.norm(l_signed_norm - identity_surface, ord="fro"))
    identity_error_op = float(np.linalg.norm(l_signed_norm - identity_surface, ord=2))
    l_eigs = np.linalg.eigvalsh(l_signed_norm)
    k_eigs = np.linalg.eigvalsh(k_matrix)
    lambda_min_l = float(np.min(l_eigs)) if len(l_eigs) else 0.0
    lambda_max_l = float(np.max(l_eigs)) if len(l_eigs) else 0.0
    lambda_min_k = float(np.min(k_eigs)) if len(k_eigs) else 0.0
    lambda_max_k = float(np.max(k_eigs)) if len(k_eigs) else 0.0
    xy_floor_spectral_lower_bound = float(max(0.0, (1.0 - lambda_max_l) / 2.0))
    signed_frame_gap_from_l = float(lambda_min_l)
    signed_frame_gap_from_k = float(1.0 - lambda_max_k)
    row.update(
        {
            "psi_pi_fraction_proxy": float(np.mean(sign_bits)) if len(sign_bits) else 0.0,
            "identity_error_fro": identity_error_fro,
            "identity_error_op": identity_error_op,
            "signed_laplacian_lambda_min": lambda_min_l,
            "signed_laplacian_lambda_max": lambda_max_l,
            "signed_laplacian_trace": float(np.trace(l_signed_norm)),
            "signed_k_lambda_min": lambda_min_k,
            "signed_k_lambda_max": lambda_max_k,
            "signed_k_trace": float(np.trace(k_matrix)),
            "signed_frame_gap_from_l": signed_frame_gap_from_l,
            "signed_frame_gap_from_k": signed_frame_gap_from_k,
            "signed_frame_gap_consistency_abs": float(abs(signed_frame_gap_from_l - signed_frame_gap_from_k)),
            "xy_floor_spectral_lower_bound": xy_floor_spectral_lower_bound,
            "xy_upper_edge_margin": float(1.0 - lambda_max_l),
        }
    )
    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    metric_rows = [row for row in rows if row.get("status") in {OK_STATUS, PARTIAL_STATUS}]
    def mean(key: str) -> float:
        values = [float(row[key]) for row in metric_rows if isinstance(row.get(key), (int, float))]
        return float(sum(values) / len(values)) if values else 0.0
    return {
        "shared_frame_shell_count": int(len(metric_rows)),
        "signed_laplacian_lambda_min_mean": mean("signed_laplacian_lambda_min"),
        "signed_laplacian_lambda_max_mean": mean("signed_laplacian_lambda_max"),
        "signed_frame_gap_from_l_mean": mean("signed_frame_gap_from_l"),
        "signed_frame_gap_from_k_mean": mean("signed_frame_gap_from_k"),
        "xy_floor_spectral_lower_bound_mean": mean("xy_floor_spectral_lower_bound"),
        "identity_error_op_mean": mean("identity_error_op"),
        "identity_error_fro_mean": mean("identity_error_fro"),
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
            "shells": shells,
            "seed": int(args.seed),
        },
        "status": ERROR_STATUS if any(s == ERROR_STATUS for s in statuses) else (PARTIAL_STATUS if any(s == PARTIAL_STATUS for s in statuses) else OK_STATUS),
        "rows": rows,
        "aggregate": _aggregate_rows(rows),
        "warnings": warnings,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
