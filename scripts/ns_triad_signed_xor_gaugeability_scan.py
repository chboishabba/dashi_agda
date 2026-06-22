#!/usr/bin/env python3
"""Scan signed mod-2 gaugeability telemetry for the active NS Wall 1 route."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
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


SCRIPT_NAME = "scripts/ns_triad_signed_xor_gaugeability_scan.py"
CONTRACT = "ns_triad_signed_xor_gaugeability_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_XOR_GAUGEABILITY_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_xor_gaugeability_scan_N128_20260622.json"
)
DEFAULT_SHELLS = (2, 3)
MAX_EXACT_MODE_COUNT = 18

CONTROL_CARD = {
    "O": "Measure signed mod-2 gaugeability telemetry on the active NS Wall 1 shell carrier.",
    "R": (
        "Project the triad sign pattern onto a Z2 gaugeability surface, measure weighted distance "
        "to im(B2), and separate sign balance from actual non-gaugeability."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; the signed-XOR distance surface is empirical and non-promoting.",
    "L": (
        "Load raw frames, select shell carriers, build resonant triads, extract the oracle sign pattern, "
        "solve the shellwise weighted mod-2 gaugeability problem, and emit fail-closed summary metrics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this scan.",
    "F": "The scan measures weighted distance to im(B2) only; it does not prove a uniform non-gaugeability theorem.",
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


def _gf2_rank(matrix: np.ndarray) -> int:
    mat = np.asarray(matrix % 2, dtype=np.uint8).copy()
    rows, cols = mat.shape
    rank = 0
    pivot_row = 0
    for col in range(cols):
        pivot = None
        for row in range(pivot_row, rows):
            if int(mat[row, col]) == 1:
                pivot = row
                break
        if pivot is None:
            continue
        if pivot != pivot_row:
            mat[[pivot_row, pivot]] = mat[[pivot, pivot_row]]
        for row in range(rows):
            if row != pivot_row and int(mat[row, col]) == 1:
                mat[row] ^= mat[pivot_row]
        rank += 1
        pivot_row += 1
        if pivot_row >= rows:
            break
    return int(rank)


def _oracle_sign_bits(target_cocycle: np.ndarray) -> np.ndarray:
    bits = []
    for angle in np.asarray(target_cocycle, dtype=np.float64):
        wrapped = float(_wrap_phase(float(angle)))
        zero_dist = abs(wrapped)
        pi_dist = abs(_wrap_phase(wrapped - math.pi))
        bits.append(1 if pi_dist < zero_dist else 0)
    return np.asarray(bits, dtype=np.uint8)


def _weighted_sign_balance(sign_bits: np.ndarray, weights: np.ndarray, zero_eps: float) -> dict[str, float]:
    safe_weights = np.maximum(np.asarray(weights, dtype=np.float64), float(zero_eps))
    total_weight = float(np.sum(safe_weights))
    if total_weight <= 0.0:
        total_weight = 1.0
    pi_weight = float(np.sum(safe_weights[np.asarray(sign_bits, dtype=bool)]))
    zero_weight = float(total_weight - pi_weight)
    pi_fraction = float(pi_weight / total_weight)
    return {
        "psi_pi_weight_fraction": pi_fraction,
        "psi_zero_weight_fraction": float(zero_weight / total_weight),
        "psi_sign_balance_gap_abs": float(abs(pi_fraction - 0.5)),
        "psi_pi_weight": pi_weight,
        "psi_zero_weight": zero_weight,
        "total_weight": total_weight,
    }


def _weighted_gauge_distance(
    row_support: list[tuple[int, int, int]],
    sign_bits: np.ndarray,
    weights: np.ndarray,
    mode_count: int,
) -> dict[str, float | int | bool]:
    if mode_count > MAX_EXACT_MODE_COUNT:
        return {
            "exact_solver_used": False,
            "gaugeable": False,
            "weighted_distance": 0.0,
            "weighted_distance_fraction": 0.0,
            "best_assignment_index": -1,
            "minimum_violated_edge_count": 0,
        }
    best_weight = math.inf
    best_edge_count = 0
    best_index = 0
    total_weight = float(np.sum(weights)) if len(weights) else 1.0
    if total_weight <= 0.0:
        total_weight = 1.0
    for assign_index, mask in enumerate(range(1 << mode_count)):
        violated_weight = 0.0
        violated_edges = 0
        for edge_index, (left, right, out) in enumerate(row_support):
            parity = ((mask >> left) ^ (mask >> right) ^ (mask >> out)) & 1
            if parity != int(sign_bits[edge_index]):
                violated_weight += float(weights[edge_index])
                violated_edges += 1
                if violated_weight >= best_weight:
                    break
        if violated_weight < best_weight - 1.0e-12:
            best_weight = violated_weight
            best_edge_count = violated_edges
            best_index = assign_index
    if not math.isfinite(best_weight):
        best_weight = 0.0
    return {
        "exact_solver_used": True,
        "gaugeable": bool(best_weight <= 1.0e-12),
        "weighted_distance": float(best_weight),
        "weighted_distance_fraction": float(best_weight / total_weight),
        "best_assignment_index": int(best_index),
        "minimum_violated_edge_count": int(best_edge_count),
    }


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
        row["errors"] = [f"signed_xor_gaugeability_scan_error: {exc}"]
        return ERROR_STATUS, row

    mode_count = int(len(shell_modes))
    triad_count = int(len(triad_links))
    row["selected_mode_count"] = mode_count
    row["triad_count"] = triad_count
    row["oracle_reference_unique_count"] = int(oracle_metrics["oracle_reference_unique_count"])
    row["oracle_local_vs_global_disagreement_fraction"] = float(
        oracle_metrics["oracle_local_vs_global_disagreement_fraction"]
    )

    if triad_count == 0 or mode_count == 0:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_modes"]
        return PARTIAL_STATUS, row

    sign_bits = _oracle_sign_bits(oracle_target)
    weights = np.asarray([float(link.weight) for link in triad_links], dtype=np.float64)
    balance = _weighted_sign_balance(sign_bits, weights, zero_eps=zero_eps)
    b2 = np.zeros((triad_count, mode_count), dtype=np.uint8)
    row_support: list[tuple[int, int, int]] = []
    for edge_index, triad in enumerate(triad_links):
        left = int(triad.left)
        right = int(triad.right)
        out = int(triad.out)
        b2[edge_index, left] = 1
        b2[edge_index, right] = 1
        b2[edge_index, out] = 1
        row_support.append((left, right, out))
    rank_b2 = _gf2_rank(b2)
    rank_augmented = _gf2_rank(np.concatenate([b2, sign_bits[:, None]], axis=1))
    gauge_metrics = _weighted_gauge_distance(row_support, sign_bits, weights, mode_count=mode_count)

    min_balance_capacity = min(balance["psi_pi_weight"], balance["psi_zero_weight"])
    distance = float(gauge_metrics["weighted_distance"])
    row.update(
        {
            "psi_pi_weight_fraction": float(balance["psi_pi_weight_fraction"]),
            "psi_zero_weight_fraction": float(balance["psi_zero_weight_fraction"]),
            "psi_sign_balance_gap_abs": float(balance["psi_sign_balance_gap_abs"]),
            "psi_pi_weight": float(balance["psi_pi_weight"]),
            "psi_zero_weight": float(balance["psi_zero_weight"]),
            "signed_xor_mode_count": int(mode_count),
            "signed_xor_triad_count": int(triad_count),
            "b2_rank": int(rank_b2),
            "b2_augmented_rank": int(rank_augmented),
            "b2_nullity_proxy": int(max(mode_count - rank_b2, 0)),
            "b2_left_nullity_proxy": int(max(triad_count - rank_b2, 0)),
            "signed_xor_gaugeable": bool(gauge_metrics["gaugeable"]),
            "exact_mod2_solver_used": bool(gauge_metrics["exact_solver_used"]),
            "signed_xor_weighted_distance": distance,
            "signed_xor_weighted_distance_fraction": float(gauge_metrics["weighted_distance_fraction"]),
            "signed_xor_best_assignment_index": int(gauge_metrics["best_assignment_index"]),
            "signed_xor_minimum_violated_edge_count": int(gauge_metrics["minimum_violated_edge_count"]),
            "signed_xor_distance_vs_balance_capacity": float(distance / max(min_balance_capacity, zero_eps)),
        }
    )
    if bool(gauge_metrics["exact_solver_used"]):
        row["status"] = OK_STATUS
        return OK_STATUS, row
    row["status"] = PARTIAL_STATUS
    row["warnings"] = [f"exact_solver_skipped_mode_count_{mode_count}"]
    return PARTIAL_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    metric_rows = [row for row in rows if row.get("status") in {OK_STATUS, PARTIAL_STATUS}]
    if not metric_rows:
        return {
            "shared_frame_shell_count": 0,
            "psi_pi_weight_fraction_mean": 0.0,
            "signed_xor_weighted_distance_fraction_mean": 0.0,
            "signed_xor_distance_vs_balance_capacity_mean": 0.0,
            "signed_xor_gaugeable_fraction": 0.0,
            "wall1a_status": "unproved",
        }
    def mean(key: str) -> float:
        values = [float(row[key]) for row in metric_rows if isinstance(row.get(key), (int, float))]
        return float(sum(values) / len(values)) if values else 0.0
    return {
        "shared_frame_shell_count": int(len(metric_rows)),
        "psi_pi_weight_fraction_mean": mean("psi_pi_weight_fraction"),
        "signed_xor_weighted_distance_fraction_mean": mean("signed_xor_weighted_distance_fraction"),
        "signed_xor_distance_vs_balance_capacity_mean": mean("signed_xor_distance_vs_balance_capacity"),
        "signed_xor_gaugeable_fraction": mean("signed_xor_gaugeable"),
        "b2_rank_mean": mean("b2_rank"),
        "b2_left_nullity_proxy_mean": mean("b2_left_nullity_proxy"),
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
