#!/usr/bin/env python3
"""Scan cycle-family quadratic lower-bound telemetry for the active NS Wall 1 shell carrier."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_triad_cocycle_floor_scan import (  # type: ignore
    AUTHORITY,
    CONTRACT as SOURCE_CONTRACT,
    DEFAULT_OUTPUT_JSON as DEFAULT_COCYCLE_FLOOR_JSON,
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_SEED,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    DEFAULT_SHELLS,
    OK_STATUS,
    PARTIAL_STATUS,
    ERROR_STATUS,
    _aggregate_rows as _aggregate_cycle_rows,
    _build_incidence,
    _build_triad_links,
    _choose_best_reference,
    _collect_modes,
    _fit_phase_field,
    _frame_velocity,
    _integer_cycle_basis,
    _json_text,
    _load_raw_bundle,
    _mode_arrays,
    _mode_shell_filter,
    _scalar_vorticity_spectrum,
    _triadwise_oracle_target,
    _validate_shells,
    _wrap_phase,
)


SCRIPT_NAME = "scripts/ns_triad_cycle_family_lower_bound_scan.py"
CONTRACT = "ns_triad_cycle_family_lower_bound_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_FAMILY_LOWER_BOUND_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_family_lower_bound_scan_N128_20260622.json"
)

CONTROL_CARD = {
    "O": "Measure cycle-family quadratic lower-bound telemetry on the active NS Wall 1 shell carrier.",
    "R": (
        "Upgrade the one-cycle lower-bound surface to a family-level quadratic obstruction by building "
        "an integer cycle family, defects d, and a weighted Gram surface C W^-1 C^T."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; the family lower bound is empirical, fail-closed, and non-promoting.",
    "L": (
        "Load raw frames, select shell carriers, build resonant triads, extract an integer cycle family, "
        "form the weighted Gram surface, and emit family lower-bound support metrics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this scan.",
    "F": "The scan estimates family-level obstruction support only; it does not prove a uniform c0 > 0 floor.",
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


def _effective_rank(eigenvalues: np.ndarray, tol: float) -> float:
    positive = np.asarray([float(v) for v in eigenvalues if float(v) > float(tol)], dtype=np.float64)
    if len(positive) == 0:
        return 0.0
    total = float(np.sum(positive))
    if total <= 0.0:
        return 0.0
    p = positive / total
    entropy = float(-np.sum(p * np.log(np.maximum(p, tol))))
    return float(math.exp(entropy))


def _family_metrics(
    incidence: np.ndarray,
    weights: np.ndarray,
    target_cocycle: np.ndarray,
    zero_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, float]]:
    triad_count = int(len(weights))
    mode_count = int(incidence.shape[1]) if incidence.ndim == 2 else 0
    if triad_count == 0 or incidence.size == 0:
        return [], {
            "cycle_family_dim": 0.0,
            "cycle_family_effective_rank": 0.0,
            "cycle_family_support_coverage": 0.0,
            "cycle_family_defect_rms": 0.0,
            "cycle_family_defect_max": 0.0,
            "cycle_family_lower_bound": 0.0,
            "cycle_family_lower_bound_normalized_upper": 0.0,
            "cycle_family_upper_proxy": 0.0,
            "cycle_family_gram_trace": 0.0,
            "cycle_family_gram_rank": 0.0,
            "cycle_family_gram_condition": 0.0,
            "cycle_family_gram_min_positive_eigenvalue": 0.0,
            "cycle_family_gram_max_eigenvalue": 0.0,
            "cycle_family_pinv_trace": 0.0,
            "cycle_family_regularization": 0.0,
            "cycle_family_lower_bound_vs_single_mean_ratio": 0.0,
            "cycle_family_lower_bound_vs_single_max_ratio": 0.0,
        }

    basis = _integer_cycle_basis(incidence, zero_eps=zero_eps)
    if basis.ndim != 2 or basis.shape[0] == 0:
        return [], {
            "cycle_family_dim": 0.0,
            "cycle_family_effective_rank": 0.0,
            "cycle_family_support_coverage": 0.0,
            "cycle_family_defect_rms": 0.0,
            "cycle_family_defect_max": 0.0,
            "cycle_family_lower_bound": 0.0,
            "cycle_family_lower_bound_normalized_upper": 0.0,
            "cycle_family_upper_proxy": 0.0,
            "cycle_family_gram_trace": 0.0,
            "cycle_family_gram_rank": 0.0,
            "cycle_family_gram_condition": 0.0,
            "cycle_family_gram_min_positive_eigenvalue": 0.0,
            "cycle_family_gram_max_eigenvalue": 0.0,
            "cycle_family_pinv_trace": 0.0,
            "cycle_family_regularization": 0.0,
            "cycle_family_lower_bound_vs_single_mean_ratio": 0.0,
            "cycle_family_lower_bound_vs_single_max_ratio": 0.0,
        }

    safe_weights = np.maximum(np.asarray(weights, dtype=np.float64), float(zero_eps))
    inv_weights = 1.0 / safe_weights
    cycle_family = np.asarray(basis, dtype=np.float64)
    defects = np.asarray(
        [abs(_wrap_phase(float(np.dot(row, np.asarray(target_cocycle, dtype=np.float64))))) for row in cycle_family],
        dtype=np.float64,
    )
    gram = cycle_family @ np.diag(inv_weights) @ cycle_family.T
    gram = 0.5 * (gram + gram.T)
    eigvals = np.linalg.eigvalsh(gram) if gram.size else np.zeros(0, dtype=np.float64)
    tol = max(float(zero_eps) * 1000.0, 1.0e-12)
    positive = eigvals[eigvals > tol]
    reg = float(max(tol, 1.0e-9 * float(np.max(eigvals)) if len(eigvals) else tol))
    gram_pinv = np.linalg.pinv(gram, rcond=max(float(zero_eps), 1.0e-10)) if gram.size else np.zeros_like(gram)
    lower_bound = float((4.0 / (math.pi * math.pi)) * float(defects @ gram_pinv @ defects)) if gram.size else 0.0
    upper_proxy = float(4.0 * np.sum(safe_weights))
    normalized_upper = float(lower_bound / max(upper_proxy, float(zero_eps)))
    support_union = np.any(np.abs(cycle_family) > tol, axis=0) if cycle_family.size else np.zeros(triad_count, dtype=bool)

    family_rows: list[dict[str, Any]] = []
    diag_gram = np.diag(gram) if gram.ndim == 2 else np.zeros(0, dtype=np.float64)
    for index, row in enumerate(cycle_family[: min(12, len(cycle_family))]):
        family_rows.append(
            {
                "cycle_family_index": int(index),
                "support_count": int(np.count_nonzero(np.abs(row) > tol)),
                "defect": float(defects[index]),
                "gram_diagonal": float(diag_gram[index]) if index < len(diag_gram) else 0.0,
            }
        )

    return family_rows, {
        "cycle_family_dim": float(cycle_family.shape[0]),
        "cycle_family_effective_rank": float(_effective_rank(eigvals, tol)),
        "cycle_family_support_coverage": float(np.count_nonzero(support_union) / max(triad_count, 1)),
        "cycle_family_defect_rms": float(math.sqrt(np.mean(defects * defects))) if len(defects) else 0.0,
        "cycle_family_defect_max": float(np.max(defects)) if len(defects) else 0.0,
        "cycle_family_lower_bound": float(lower_bound),
        "cycle_family_lower_bound_normalized_upper": float(normalized_upper),
        "cycle_family_upper_proxy": float(upper_proxy),
        "cycle_family_gram_trace": float(np.trace(gram)) if gram.size else 0.0,
        "cycle_family_gram_rank": float(len(positive)),
        "cycle_family_gram_condition": float(np.max(positive) / max(np.min(positive), tol)) if len(positive) else 0.0,
        "cycle_family_gram_min_positive_eigenvalue": float(np.min(positive)) if len(positive) else 0.0,
        "cycle_family_gram_max_eigenvalue": float(np.max(positive)) if len(positive) else 0.0,
        "cycle_family_pinv_trace": float(np.trace(gram_pinv)) if gram_pinv.size else 0.0,
        "cycle_family_regularization": float(reg),
        "cycle_family_lower_bound_vs_single_mean_ratio": 0.0,
        "cycle_family_lower_bound_vs_single_max_ratio": 0.0,
    }


def _shell_row(
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
        incidence, weights, closures, shell_spreads, distinct_shells = _build_incidence(shell_modes, triad_links)
        best_reference, best_shift, reference_rows = _choose_best_reference(
            phases=phases,
            amplitudes=amplitudes,
            shell_coord=shell_coord,
            fitted_phase=fitted_phase,
            triad_links=triad_links,
            zero_eps=zero_eps,
        )
        oracle_target, oracle_metrics = _triadwise_oracle_target(
            reference_rows=reference_rows,
            triad_count=len(triad_links),
        )
        family_rows, family_metrics = _family_metrics(
            incidence=incidence,
            weights=np.asarray([float(link.weight) for link in triad_links], dtype=np.float64),
            target_cocycle=oracle_target,
            zero_eps=zero_eps,
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_cycle_family_lower_bound_scan_error: {exc}"]
        return ERROR_STATUS, row

    triad_count = len(triad_links)
    amp_sum = float(np.sum(amplitudes)) if len(amplitudes) else 0.0
    mode_concentration = float(np.max(amplitudes) / max(amp_sum, float(zero_eps))) if len(amplitudes) else 0.0
    raw_closure_mean_abs = float(np.mean(np.abs(closures))) if len(closures) else 0.0
    best_floor_proxy = float(best_reference["frustration_floor_proxy"])
    floor_ratio = float(best_floor_proxy / max(raw_closure_mean_abs, float(zero_eps)))

    single_mean = 0.0
    single_max = 0.0
    if family_rows:
        pass
    # Reuse the single-cycle producer metrics to anchor family-vs-single comparisons.
    from ns_triad_cocycle_floor_scan import _cycle_lower_bounds  # type: ignore

    _, single_metrics = _cycle_lower_bounds(
        incidence=incidence,
        weights=np.asarray([float(link.weight) for link in triad_links], dtype=np.float64),
        target_cocycle=oracle_target,
        zero_eps=zero_eps,
    )
    single_mean = float(single_metrics["mean_cycle_lower_bound"])
    single_max = float(single_metrics["max_cycle_lower_bound"])
    family_metrics["cycle_family_lower_bound_vs_single_mean_ratio"] = float(
        family_metrics["cycle_family_lower_bound"] / max(single_mean, float(zero_eps))
    )
    family_metrics["cycle_family_lower_bound_vs_single_max_ratio"] = float(
        family_metrics["cycle_family_lower_bound"] / max(single_max, float(zero_eps))
    )

    row.update(
        {
            "selected_mode_count": int(len(shell_modes)),
            "selected_mode_amplitude_sum": float(amp_sum),
            "mode_concentration_fraction": float(mode_concentration),
            "triad_count": int(triad_count),
            "best_reference_id": str(best_reference["reference_id"]),
            "best_reference_kind": str(best_reference["reference_kind"]),
            "best_reference_floor_proxy": float(best_floor_proxy),
            "best_reference_lambda_max_proxy": float(best_reference["lambda_max_proxy"]),
            "raw_closure_mean_abs": float(raw_closure_mean_abs),
            "frustration_floor_ratio_vs_raw": float(floor_ratio),
            "oracle_reference_unique_count": int(oracle_metrics["oracle_reference_unique_count"]),
            "oracle_local_vs_global_disagreement_fraction": float(oracle_metrics["oracle_local_vs_global_disagreement_fraction"]),
            "oracle_target_mean_abs": float(oracle_metrics["oracle_target_mean_abs"]),
            "shell_spread_mean": float(np.mean(shell_spreads)) if len(shell_spreads) else 0.0,
            "distinct_shell_count_mean": float(np.mean(distinct_shells)) if len(distinct_shells) else 0.0,
            "single_cycle_mean_lower_bound": float(single_mean),
            "single_cycle_max_lower_bound": float(single_max),
            "cycle_family_dim": float(family_metrics["cycle_family_dim"]),
            "cycle_family_effective_rank": float(family_metrics["cycle_family_effective_rank"]),
            "cycle_family_support_coverage": float(family_metrics["cycle_family_support_coverage"]),
            "cycle_family_defect_rms": float(family_metrics["cycle_family_defect_rms"]),
            "cycle_family_defect_max": float(family_metrics["cycle_family_defect_max"]),
            "cycle_family_lower_bound": float(family_metrics["cycle_family_lower_bound"]),
            "cycle_family_lower_bound_normalized_upper": float(family_metrics["cycle_family_lower_bound_normalized_upper"]),
            "cycle_family_upper_proxy": float(family_metrics["cycle_family_upper_proxy"]),
            "cycle_family_gram_trace": float(family_metrics["cycle_family_gram_trace"]),
            "cycle_family_gram_rank": float(family_metrics["cycle_family_gram_rank"]),
            "cycle_family_gram_condition": float(family_metrics["cycle_family_gram_condition"]),
            "cycle_family_gram_min_positive_eigenvalue": float(family_metrics["cycle_family_gram_min_positive_eigenvalue"]),
            "cycle_family_gram_max_eigenvalue": float(family_metrics["cycle_family_gram_max_eigenvalue"]),
            "cycle_family_pinv_trace": float(family_metrics["cycle_family_pinv_trace"]),
            "cycle_family_regularization": float(family_metrics["cycle_family_regularization"]),
            "cycle_family_lower_bound_vs_single_mean_ratio": float(family_metrics["cycle_family_lower_bound_vs_single_mean_ratio"]),
            "cycle_family_lower_bound_vs_single_max_ratio": float(family_metrics["cycle_family_lower_bound_vs_single_max_ratio"]),
            "cycle_family_rows_head": family_rows,
        }
    )

    warnings: list[str] = []
    if int(len(shell_modes)) < 3:
        warnings.append("shell carrier has fewer than three selected modes")
    if triad_count <= 0:
        warnings.append("no resonant triads in shell carrier")
    if float(family_metrics["cycle_family_dim"]) <= 0.0:
        warnings.append("cycle family collapsed for this shell carrier")
    if float(family_metrics["cycle_family_lower_bound"]) <= float(zero_eps):
        warnings.append("cycle-family lower bound collapsed to zero on this shell carrier")
    if warnings:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = warnings
        return PARTIAL_STATUS, row

    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]], shells: list[int]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            value = row.get(key)
            if isinstance(value, (int, float)) and math.isfinite(float(value)):
                values.append(float(value))
        return values

    return {
        "processed_rows": int(len(rows)),
        "ok_rows": int(sum(1 for row in rows if row.get("status") == OK_STATUS)),
        "partial_rows": int(sum(1 for row in rows if row.get("status") == PARTIAL_STATUS)),
        "error_rows": int(sum(1 for row in rows if row.get("status") == ERROR_STATUS)),
        "shells": [int(shell) for shell in shells],
        "top_k": int(ok_rows[0]["top_k"]) if ok_rows else None,
        "cycle_family_dim_mean": float(np.mean(_series("cycle_family_dim"))) if _series("cycle_family_dim") else None,
        "cycle_family_effective_rank_mean": float(np.mean(_series("cycle_family_effective_rank"))) if _series("cycle_family_effective_rank") else None,
        "cycle_family_support_coverage_mean": float(np.mean(_series("cycle_family_support_coverage"))) if _series("cycle_family_support_coverage") else None,
        "cycle_family_lower_bound_mean": float(np.mean(_series("cycle_family_lower_bound"))) if _series("cycle_family_lower_bound") else None,
        "cycle_family_lower_bound_normalized_upper_mean": float(np.mean(_series("cycle_family_lower_bound_normalized_upper")))
        if _series("cycle_family_lower_bound_normalized_upper")
        else None,
        "cycle_family_gram_condition_mean": float(np.mean(_series("cycle_family_gram_condition"))) if _series("cycle_family_gram_condition") else None,
        "cycle_family_gram_rank_mean": float(np.mean(_series("cycle_family_gram_rank"))) if _series("cycle_family_gram_rank") else None,
        "cycle_family_regularization_mean": float(np.mean(_series("cycle_family_regularization"))) if _series("cycle_family_regularization") else None,
        "cycle_family_lower_bound_vs_single_mean_ratio_mean": float(np.mean(_series("cycle_family_lower_bound_vs_single_mean_ratio")))
        if _series("cycle_family_lower_bound_vs_single_mean_ratio")
        else None,
        "cycle_family_lower_bound_vs_single_max_ratio_mean": float(np.mean(_series("cycle_family_lower_bound_vs_single_max_ratio")))
        if _series("cycle_family_lower_bound_vs_single_max_ratio")
        else None,
        "cycle_family_vs_floor_ratio_correlation": _pearson(
            _series("cycle_family_lower_bound_normalized_upper"),
            _series("frustration_floor_ratio_vs_raw"),
        ),
        "cycle_family_vs_oracle_disagreement_correlation": _pearson(
            _series("cycle_family_lower_bound_normalized_upper"),
            _series("oracle_local_vs_global_disagreement_fraction"),
        ),
        "cycle_family_vs_single_mean_ratio_correlation": _pearson(
            _series("cycle_family_lower_bound_vs_single_mean_ratio"),
            _series("cycle_family_lower_bound_normalized_upper"),
        ),
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells)
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    snapshots = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)

    if not snapshots:
        payload = {
            "contract": CONTRACT,
            "schema_version": SCHEMA_VERSION,
            "route_decision": ROUTE_DECISION,
            "script_name": SCRIPT_NAME,
            "control_card": CONTROL_CARD,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": ["no frames selected"],
            "warnings": warnings,
            "rows": [],
            "aggregate": _aggregate_rows([], shells),
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    rows: list[dict[str, Any]] = []
    for slot, snapshot in enumerate(snapshots):
        for shell_n in shells:
            _status, row = _shell_row(
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
        "source_contract_dependency": SOURCE_CONTRACT,
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
            "shells": [int(shell) for shell in shells],
            "seed": int(args.seed),
            "zero_eps": float(args.zero_eps),
        },
        "rows": rows,
        "aggregate": _aggregate_rows(rows, shells),
    }
    payload["status"] = OK_STATUS if not any(row.get("status") == ERROR_STATUS for row in rows) else PARTIAL_STATUS
    payload["ok"] = payload["status"] == OK_STATUS

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
