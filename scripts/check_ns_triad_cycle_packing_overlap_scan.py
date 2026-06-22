#!/usr/bin/env python3
"""Validate ns_triad_cycle_packing_overlap_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_cycle_packing_overlap_scan.py"
CONTRACT = "check_ns_triad_cycle_packing_overlap_scan"
SOURCE_CONTRACT = "ns_triad_cycle_packing_overlap_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_cycle_packing_overlap_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_PACKING_OVERLAP_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_PACKING_OVERLAP_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_packing_overlap_scan_N128_20260622.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_cycle_packing_overlap_scan_N128_20260622.json"
)

EXPECTED_AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}

SOURCE_CONTRACT_DEPENDENCY = "ns_triad_cocycle_floor_scan"
CONTROL_CARD = {
    "O": "Measure shellwise cycle-family packing and overlap telemetry on the active NS Wall 1 carrier.",
    "R": (
        "Build an integer cycle family, analyze support overlap and weighted Gram conditioning, "
        "and flag whether obstruction directions collapse under the shell carrier."
    ),
    "C": SOURCE_SCRIPT_NAME,
    "S": "Candidate-only telemetry; the packing/overlap surface is empirical and non-promoting.",
    "L": (
        "Load raw frames, select shell carriers, build resonant triads, extract an integer cycle family, "
        "and summarize overlap, concentration, and collapse telemetry."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "The scan estimates cycle-family packing structure only; it does not prove a uniform lower bound.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_json", nargs="?", type=Path)
    parser.add_argument("--source-json", type=Path, dest="source_json_kw")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _input_path(args: argparse.Namespace) -> Path:
    if args.source_json is not None and args.source_json_kw is not None:
        raise ValueError("provide either positional source_json or --source-json, not both")
    if args.source_json is None and args.source_json_kw is None:
        return DEFAULT_SOURCE_JSON
    return args.source_json if args.source_json is not None else args.source_json_kw


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("payload must be object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _positive_int(value: Any) -> int | None:
    parsed = _nonnegative_int(value)
    if parsed is None or parsed <= 0:
        return None
    return parsed


def _check_fraction(errors: list[str], path: str, value: Any) -> None:
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        errors.append(f"{path}: must be finite fraction in [0,1]")


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key, expected in CONTROL_CARD.items():
        if payload.get(key) != expected:
            errors.append(f"{key}: must be {expected!r}")
    control_card = payload.get("control_card")
    if not isinstance(control_card, dict):
        errors.append("control_card: must be object")
        return
    for key, expected in CONTROL_CARD.items():
        if control_card.get(key) != expected:
            errors.append(f"control_card.{key}: must be {expected!r}")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
        return
    for key, expected_value in EXPECTED_AUTHORITY.items():
        if authority.get(key) is not expected_value:
            errors.append(f"authority.{key}: must be {expected_value!r}")


def _check_optional_list(errors: list[str], path: str, value: Any) -> None:
    if value is not None and not isinstance(value, list):
        errors.append(f"{path}: must be list or null")


def _check_optional_object(errors: list[str], path: str, value: Any) -> None:
    if value is not None and not isinstance(value, dict):
        errors.append(f"{path}: must be object or null")


def _check_row_metrics(row: dict[str, Any], path: str, errors: list[str]) -> None:
    for key in ("frame", "snapshot_index", "shell", "top_k", "pool_multiplier"):
        if _nonnegative_int(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int")
    if _positive_int(row.get("shell")) is None:
        errors.append(f"{path}.shell: must be positive int")
    if _positive_int(row.get("top_k")) is None:
        errors.append(f"{path}.top_k: must be positive int")
    if _positive_int(row.get("pool_multiplier")) is None:
        errors.append(f"{path}.pool_multiplier: must be positive int")

    if row.get("route_family") != "Wall 1":
        errors.append(f"{path}.route_family: must be 'Wall 1'")
    if _finite_float(row.get("zero_eps")) is None or _finite_float(row.get("zero_eps")) <= 0.0:
        errors.append(f"{path}.zero_eps: must be finite positive")
    if row.get("cycle_family_regularization_applied") not in (True, False):
        errors.append(f"{path}.cycle_family_regularization_applied: must be bool")

    for key in (
        "selected_mode_count",
        "triad_count",
        "oracle_reference_unique_count",
    ):
        if _nonnegative_int(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int")
    for key in (
        "selected_mode_amplitude_sum",
        "mode_concentration_fraction",
        "phase_field_fit_rmse",
        "best_reference_floor_proxy",
        "best_reference_lambda_max_proxy",
        "oracle_local_vs_global_disagreement_fraction",
        "oracle_target_mean_abs",
        "shell_spread_mean",
        "shell_spread_p95",
        "cycle_family_dim",
        "cycle_family_effective_rank",
        "cycle_family_support_coverage",
        "cycle_family_defect_rms",
        "cycle_family_defect_max",
        "cycle_family_lower_bound",
        "cycle_family_lower_bound_max",
        "cycle_family_lower_bound_normalized_max",
        "cycle_family_lower_bound_normalized_upper",
        "cycle_family_lower_bound_normalized_mean",
        "cycle_family_lower_bound_normalized_sum",
        "cycle_family_lower_bound_support_weighted_sum",
        "cycle_family_lower_bound_support_over_F_max",
        "cycle_family_lower_bound_joint",
        "cycle_family_lower_bound_joint_over_F_max",
        "cycle_family_upper_proxy_raw",
        "cycle_family_upper_proxy",
        "cycle_family_bound_inversion_gap",
        "cycle_family_F_max",
        "cycle_family_gram_trace",
        "cycle_family_gram_rank",
        "cycle_family_gram_condition",
        "cycle_family_gram_effective_rank",
        "cycle_family_gram_min_positive_eigenvalue",
        "cycle_family_gram_max_eigenvalue",
        "cycle_family_gram_regularized_min_eig",
        "cycle_family_gram_regularized_max_eig",
        "cycle_family_gram_regularized_condition",
        "cycle_family_gram_regularized_effective_rank",
        "cycle_family_regularization_ridge",
        "cycle_family_packing_concentration",
        "cycle_family_packing_entropy_normalized",
        "cycle_family_packing_effective_count",
        "cycle_family_support_overlap_mean",
        "cycle_family_support_overlap_max",
        "cycle_family_support_overlap_p95",
        "cycle_family_support_overlap_density",
        "cycle_family_support_overlap_row_mean",
        "cycle_family_support_overlap_row_max",
        "cycle_family_edge_usage_max",
        "cycle_family_edge_usage_entropy_normalized",
        "cycle_family_edge_usage_effective_count",
        "cycle_family_normalized_support_vs_F_max",
        "cycle_family_obstruction_collapse_score",
    ):
        value = _finite_float(row.get(key))
        if value is None:
            errors.append(f"{path}.{key}: must be finite")
            continue
        if key in {
            "mode_concentration_fraction",
            "oracle_local_vs_global_disagreement_fraction",
            "cycle_family_support_coverage",
            "cycle_family_lower_bound_normalized_max",
            "cycle_family_lower_bound_normalized_upper",
            "cycle_family_packing_concentration",
            "cycle_family_packing_entropy_normalized",
            "cycle_family_support_overlap_mean",
            "cycle_family_support_overlap_max",
            "cycle_family_support_overlap_p95",
            "cycle_family_support_overlap_density",
            "cycle_family_edge_usage_entropy_normalized",
            "cycle_family_obstruction_collapse_score",
        } and (value < -1.0e-12 or value > 1.0 + 1.0e-12):
            errors.append(f"{path}.{key}: must be within [0,1]")
        elif key in {
            "selected_mode_amplitude_sum",
            "phase_field_fit_rmse",
            "best_reference_floor_proxy",
            "best_reference_lambda_max_proxy",
            "oracle_target_mean_abs",
            "shell_spread_mean",
            "shell_spread_p95",
            "cycle_family_dim",
            "cycle_family_effective_rank",
            "cycle_family_defect_rms",
            "cycle_family_defect_max",
            "cycle_family_lower_bound",
            "cycle_family_lower_bound_max",
            "cycle_family_lower_bound_normalized_mean",
            "cycle_family_lower_bound_normalized_sum",
            "cycle_family_lower_bound_support_weighted_sum",
            "cycle_family_lower_bound_support_over_F_max",
            "cycle_family_lower_bound_joint",
            "cycle_family_lower_bound_joint_over_F_max",
            "cycle_family_upper_proxy_raw",
            "cycle_family_upper_proxy",
            "cycle_family_bound_inversion_gap",
            "cycle_family_F_max",
            "cycle_family_gram_trace",
            "cycle_family_gram_rank",
            "cycle_family_gram_condition",
            "cycle_family_gram_effective_rank",
            "cycle_family_gram_min_positive_eigenvalue",
            "cycle_family_gram_max_eigenvalue",
            "cycle_family_gram_regularized_min_eig",
            "cycle_family_gram_regularized_max_eig",
            "cycle_family_gram_regularized_condition",
            "cycle_family_gram_regularized_effective_rank",
            "cycle_family_regularization_ridge",
            "cycle_family_packing_effective_count",
            "cycle_family_support_overlap_row_mean",
            "cycle_family_support_overlap_row_max",
            "cycle_family_edge_usage_max",
        } and value < -1.0e-12:
            errors.append(f"{path}.{key}: must be nonnegative")
        elif key in {
            "cycle_family_gram_condition",
            "cycle_family_gram_regularized_condition",
        } and value < 0.0:
            errors.append(f"{path}.{key}: must be nonnegative")

    dim = _finite_float(row.get("cycle_family_dim"))
    eff_rank = _finite_float(row.get("cycle_family_effective_rank"))
    if dim is not None and eff_rank is not None and eff_rank > dim + 1.0e-12:
        errors.append(f"{path}.cycle_family_effective_rank: must not exceed dimension")
    gram_rank = _finite_float(row.get("cycle_family_gram_rank"))
    gram_eff = _finite_float(row.get("cycle_family_gram_effective_rank"))
    if dim is not None and gram_rank is not None and gram_rank > dim + 1.0e-12:
        errors.append(f"{path}.cycle_family_gram_rank: must not exceed dimension")
    if gram_eff is not None and gram_rank is not None and gram_eff > gram_rank + 1.0e-12:
        errors.append(f"{path}.cycle_family_gram_effective_rank: must not exceed gram rank")

    gram_min = _finite_float(row.get("cycle_family_gram_min_positive_eigenvalue"))
    gram_max = _finite_float(row.get("cycle_family_gram_max_eigenvalue"))
    gram_cond = _finite_float(row.get("cycle_family_gram_condition"))
    reg_min = _finite_float(row.get("cycle_family_gram_regularized_min_eig"))
    reg_max = _finite_float(row.get("cycle_family_gram_regularized_max_eig"))
    reg_cond = _finite_float(row.get("cycle_family_gram_regularized_condition"))
    reg_eff = _finite_float(row.get("cycle_family_gram_regularized_effective_rank"))
    if gram_min is not None and gram_max is not None and gram_max + 1.0e-12 < gram_min:
        errors.append(f"{path}.cycle_family_gram_max_eigenvalue: must dominate min positive eigenvalue")
    if reg_min is not None and reg_max is not None and reg_max + 1.0e-12 < reg_min:
        errors.append(f"{path}.cycle_family_gram_regularized_max_eig: must dominate min regularized eigenvalue")
    if gram_cond is not None and gram_min is not None and gram_max is not None and gram_min > 0.0:
        expected = gram_max / gram_min
        if abs(gram_cond - expected) > max(1.0e-6, 1.0e-6 * expected):
            errors.append(f"{path}.cycle_family_gram_condition: inconsistent with eigenvalue ratio")
    if reg_cond is not None and reg_min is not None and reg_max is not None and reg_min > 0.0:
        expected = reg_max / reg_min
        if abs(reg_cond - expected) > max(1.0e-6, 1.0e-6 * expected):
            errors.append(f"{path}.cycle_family_gram_regularized_condition: inconsistent with eigenvalue ratio")
    if reg_eff is not None and gram_eff is not None and reg_eff + 1.0e-12 < gram_eff:
        errors.append(f"{path}.cycle_family_gram_regularized_effective_rank: must dominate unregularized effective rank")

    lower_bound = _finite_float(row.get("cycle_family_lower_bound"))
    lower_bound_max = _finite_float(row.get("cycle_family_lower_bound_max"))
    lower_bound_norm_max = _finite_float(row.get("cycle_family_lower_bound_normalized_max"))
    lower_bound_norm_upper = _finite_float(row.get("cycle_family_lower_bound_normalized_upper"))
    lower_bound_norm_mean = _finite_float(row.get("cycle_family_lower_bound_normalized_mean"))
    lower_bound_norm_sum = _finite_float(row.get("cycle_family_lower_bound_normalized_sum"))
    support_weighted_sum = _finite_float(row.get("cycle_family_lower_bound_support_weighted_sum"))
    upper_proxy_raw = _finite_float(row.get("cycle_family_upper_proxy_raw"))
    upper_proxy = _finite_float(row.get("cycle_family_upper_proxy"))
    inversion_gap = _finite_float(row.get("cycle_family_bound_inversion_gap"))
    inversion_detected = row.get("cycle_family_bound_inversion_detected")
    bound_consistent = row.get("cycle_family_bound_consistent")
    f_max = _finite_float(row.get("cycle_family_F_max"))
    if lower_bound is not None and upper_proxy is not None and lower_bound > upper_proxy + 1.0e-12:
        errors.append(f"{path}.cycle_family_lower_bound: must not exceed upper proxy")
    if (
        lower_bound is not None
        and upper_proxy_raw is not None
        and inversion_gap is not None
        and abs(max(0.0, lower_bound - upper_proxy_raw) - inversion_gap) > max(1.0e-6, 1.0e-6 * max(lower_bound, 1.0))
    ):
        errors.append(f"{path}.cycle_family_bound_inversion_gap: inconsistent with raw upper proxy")
    if inversion_detected not in (None, True, False):
        errors.append(f"{path}.cycle_family_bound_inversion_detected: must be bool or null")
    if bound_consistent not in (None, True, False):
        errors.append(f"{path}.cycle_family_bound_consistent: must be bool or null")
    if inversion_detected is not None and inversion_gap is not None and bool(inversion_detected) != (inversion_gap > 1.0e-12):
        errors.append(f"{path}.cycle_family_bound_inversion_detected: must match inversion gap")
    if inversion_detected is not None and bound_consistent is not None and bool(bound_consistent) == bool(inversion_detected):
        errors.append(f"{path}.cycle_family_bound_consistent: must negate inversion_detected")
    for name, value in (
        ("cycle_family_lower_bound_normalized_max", lower_bound_norm_max),
        ("cycle_family_lower_bound_normalized_upper", lower_bound_norm_upper),
        ("cycle_family_lower_bound_normalized_mean", lower_bound_norm_mean),
        ("cycle_family_lower_bound_normalized_sum", lower_bound_norm_sum),
    ):
        if value is not None and (value < -1.0e-12 or value > 1.0 + 1.0e-12):
            errors.append(f"{path}.{name}: must be within [0,1]")

    pack_conc = _finite_float(row.get("cycle_family_packing_concentration"))
    pack_entropy = _finite_float(row.get("cycle_family_packing_entropy_normalized"))
    pack_eff = _finite_float(row.get("cycle_family_packing_effective_count"))
    edge_eff = _finite_float(row.get("cycle_family_edge_usage_effective_count"))
    if pack_conc is not None and pack_conc > 1.0 + 1.0e-12:
        errors.append(f"{path}.cycle_family_packing_concentration: must be within [0,1]")
    if pack_eff is not None and edge_eff is not None and abs(pack_eff - edge_eff) > 1.0e-6:
        errors.append(f"{path}.cycle_family_packing_effective_count: must match edge usage effective count")
    if pack_entropy is not None and (pack_entropy < -1.0e-12 or pack_entropy > 1.0 + 1.0e-12):
        errors.append(f"{path}.cycle_family_packing_entropy_normalized: must be within [0,1]")

    collapse = row.get("cycle_family_obstruction_directions_collapsed")
    if collapse not in (True, False):
        errors.append(f"{path}.cycle_family_obstruction_directions_collapsed: must be bool")
    if row.get("cycle_family_obstruction_collapse_reason") is not None and not isinstance(
        row.get("cycle_family_obstruction_collapse_reason"), list
    ):
        errors.append(f"{path}.cycle_family_obstruction_collapse_reason: must be list or null")
    if row.get("cycle_family_regularization_reason") is not None and not isinstance(
        row.get("cycle_family_regularization_reason"), list
    ):
        errors.append(f"{path}.cycle_family_regularization_reason: must be list or null")
    if row.get("cycle_family_rows_head") is not None and not isinstance(row.get("cycle_family_rows_head"), list):
        errors.append(f"{path}.cycle_family_rows_head: must be list or null")
    if row.get("cycle_family_support_overlap_matrix") is not None and not isinstance(
        row.get("cycle_family_support_overlap_matrix"), list
    ):
        errors.append(f"{path}.cycle_family_support_overlap_matrix: must be list or null")

    _check_optional_list(errors, f"{path}.warnings", row.get("warnings"))
    _check_optional_list(errors, f"{path}.errors", row.get("errors"))


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    status = row.get("status")
    if status not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    if row.get("fail_closed") is not None and row.get("fail_closed") is not True:
        errors.append(f"{path}.fail_closed: if present must be true")
    if row.get("candidate_only") is not True:
        errors.append(f"{path}.candidate_only: must be true")
    if row.get("empirical_non_promoting") is not True:
        errors.append(f"{path}.empirical_non_promoting: must be true")
    if row.get("promoted") is not None and row.get("promoted") is not False:
        errors.append(f"{path}.promoted: if present must be false")

    if status == ERROR_STATUS:
        errors_list = row.get("errors")
        if not isinstance(errors_list, list) or not errors_list:
            errors.append(f"{path}.errors: error rows must have a non-empty errors list")

    _check_row_metrics(row, path, errors)


def _check_aggregate(
    aggregate: dict[str, Any],
    rows: list[dict[str, Any]],
    errors: list[str],
) -> None:
    row_count = len(rows)
    processed_rows = _nonnegative_int(aggregate.get("processed_rows"))
    if processed_rows is None:
        errors.append("aggregate.processed_rows: must be nonnegative int")
        processed_rows = 0
    if processed_rows != row_count:
        errors.append("aggregate.processed_rows: must match row count")

    for key in ("ok_rows", "partial_rows", "error_rows"):
        if _nonnegative_int(aggregate.get(key)) is None:
            errors.append(f"aggregate.{key}: must be nonnegative int")

    if all(_nonnegative_int(aggregate.get(key)) is not None for key in ("ok_rows", "partial_rows", "error_rows")):
        total = int(aggregate.get("ok_rows", 0)) + int(aggregate.get("partial_rows", 0)) + int(
            aggregate.get("error_rows", 0)
        )
        if total != processed_rows:
            errors.append("aggregate row status counts must sum to processed_rows")

    shells = aggregate.get("shells")
    if not isinstance(shells, list) or not shells:
        errors.append("aggregate.shells: must be non-empty list")
    else:
        for index, shell in enumerate(shells):
            if _positive_int(shell) is None:
                errors.append(f"aggregate.shells[{index}]: must be positive int")

    if _positive_int(aggregate.get("top_k")) is None:
        errors.append("aggregate.top_k: must be positive int")
    if _positive_int(aggregate.get("pool_multiplier")) is None:
        errors.append("aggregate.pool_multiplier: must be positive int")
    zero_eps = _finite_float(aggregate.get("zero_eps"))
    if zero_eps is None or zero_eps <= 0.0:
        errors.append("aggregate.zero_eps: must be finite positive")
    if _finite_float(aggregate.get("gamma")) is None:
        errors.append("aggregate.gamma: must be finite")
    if _finite_float(aggregate.get("condition_threshold")) is None:
        errors.append("aggregate.condition_threshold: must be finite")

    for key in (
        "family_dim_mean",
        "family_effective_rank_mean",
        "family_support_overlap_mean",
        "family_support_overlap_max_mean",
        "family_packing_concentration_mean",
        "family_packing_entropy_normalized_mean",
        "family_regularization_rate",
        "family_gram_condition_mean",
        "family_gram_regularized_condition_mean",
        "family_gram_regularized_effective_rank_mean",
        "family_lower_bound_mean",
        "family_lower_bound_normalized_max_mean",
        "family_lower_bound_normalized_sum_mean",
        "family_lower_bound_support_weighted_sum_mean",
        "family_F_max_mean",
        "family_normalized_support_vs_F_max_mean",
        "family_obstruction_collapse_score_mean",
        "family_obstruction_directions_collapsed_rate",
    ):
        value = aggregate.get(key)
        if value is None:
            errors.append(f"aggregate.{key}: must be present")
            continue
        parsed = _finite_float(value)
        if parsed is None:
            errors.append(f"aggregate.{key}: must be finite")
            continue
        if key in {
            "family_support_overlap_mean",
            "family_support_overlap_max_mean",
            "family_packing_concentration_mean",
            "family_packing_entropy_normalized_mean",
            "family_regularization_rate",
            "family_obstruction_collapse_score_mean",
            "family_obstruction_directions_collapsed_rate",
        } and (parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12):
            errors.append(f"aggregate.{key}: must be within [0,1]")
        elif key.endswith("_mean") and parsed < -1.0e-12:
            errors.append(f"aggregate.{key}: must be nonnegative")

    normalized_mean = _finite_float(aggregate.get("family_lower_bound_normalized_max_mean"))
    if normalized_mean is not None and (normalized_mean < -1.0e-12 or normalized_mean > 1.0 + 1.0e-12):
        errors.append("aggregate.family_lower_bound_normalized_max_mean: must be within [0,1]")

    support_mean = _finite_float(aggregate.get("family_support_overlap_mean"))
    if support_mean is not None and (support_mean < -1.0e-12 or support_mean > 1.0 + 1.0e-12):
        errors.append("aggregate.family_support_overlap_mean: must be within [0,1]")

    gram_min_mean = None
    gram_max_mean = None
    gram_cond_mean = _finite_float(aggregate.get("family_gram_condition_mean"))
    if gram_min_mean is not None and gram_max_mean is not None and gram_max_mean + 1.0e-12 < gram_min_mean:
        errors.append("aggregate.family_gram_max_mean: must dominate min mean")
    if gram_cond_mean is not None and gram_min_mean is not None and gram_max_mean is not None and gram_min_mean > 0.0:
        expected = gram_max_mean / gram_min_mean
        if abs(gram_cond_mean - expected) > max(1.0e-6, 1.0e-6 * expected):
            errors.append("aggregate.family_gram_condition_mean: inconsistent with eigenvalue ratio")

    lower_bound_mean = _finite_float(aggregate.get("family_lower_bound_mean"))
    upper_proxy_mean = _finite_float(aggregate.get("family_upper_proxy_mean"))
    if lower_bound_mean is not None and upper_proxy_mean is not None and lower_bound_mean > upper_proxy_mean + 1.0e-12:
        errors.append("aggregate.family_lower_bound_mean: must not exceed upper proxy mean")

    family_rows = aggregate.get("family_rows")
    if not isinstance(family_rows, list) or len(family_rows) != row_count:
        errors.append("aggregate.family_rows: must mirror triad_cycle_packing_overlap_rows")
    elif family_rows != rows:
        errors.append("aggregate.family_rows: must exactly mirror triad_cycle_packing_overlap_rows")

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in rows:
            value = _finite_float(row.get(key))
            if value is not None:
                values.append(value)
        return values

    def _mean_matches(key: str, agg_key: str, tolerance: float = 1.0e-8) -> None:
        series = _series(key)
        aggregate_value = _finite_float(aggregate.get(agg_key))
        if aggregate_value is None:
            return
        if series:
            expected = sum(series) / float(len(series))
            if abs(aggregate_value - expected) > max(tolerance, tolerance * abs(expected)):
                errors.append(f"aggregate.{agg_key}: must match row-wise mean of {key}")

    for key, agg_key in (
        ("cycle_family_dim", "family_dim_mean"),
        ("cycle_family_effective_rank", "family_effective_rank_mean"),
        ("cycle_family_support_overlap_mean", "family_support_overlap_mean"),
        ("cycle_family_support_overlap_max", "family_support_overlap_max_mean"),
        ("cycle_family_packing_concentration", "family_packing_concentration_mean"),
        ("cycle_family_packing_entropy_normalized", "family_packing_entropy_normalized_mean"),
        ("cycle_family_gram_condition", "family_gram_condition_mean"),
        ("cycle_family_gram_regularized_condition", "family_gram_regularized_condition_mean"),
        ("cycle_family_gram_regularized_effective_rank", "family_gram_regularized_effective_rank_mean"),
        ("cycle_family_lower_bound", "family_lower_bound_mean"),
        ("cycle_family_lower_bound_normalized_max", "family_lower_bound_normalized_max_mean"),
        ("cycle_family_lower_bound_normalized_sum", "family_lower_bound_normalized_sum_mean"),
        ("cycle_family_lower_bound_support_weighted_sum", "family_lower_bound_support_weighted_sum_mean"),
        ("cycle_family_F_max", "family_F_max_mean"),
        ("cycle_family_normalized_support_vs_F_max", "family_normalized_support_vs_F_max_mean"),
        ("cycle_family_obstruction_collapse_score", "family_obstruction_collapse_score_mean"),
    ):
        _mean_matches(key, agg_key)

    regularized_rate = _finite_float(aggregate.get("family_regularization_rate"))
    if regularized_rate is not None:
        expected_regularized = sum(1 for row in rows if row.get("cycle_family_regularization_applied") is True) / float(row_count or 1)
        if abs(regularized_rate - expected_regularized) > 1.0e-8:
            errors.append("aggregate.family_regularization_rate: must match row-wise regularization rate")

    collapse_rate = _finite_float(aggregate.get("family_obstruction_directions_collapsed_rate"))
    if collapse_rate is not None:
        expected_collapse = sum(1 for row in rows if row.get("cycle_family_obstruction_directions_collapsed") is True) / float(
            row_count or 1
        )
        if abs(collapse_rate - expected_collapse) > 1.0e-8:
            errors.append("aggregate.family_obstruction_directions_collapsed_rate: must match row-wise collapse rate")


def _check_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")
    if payload.get("script") != SOURCE_SCRIPT_NAME:
        errors.append(f"script: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append(f"status: must be one of {sorted(ALLOWED_STATUSES)!r}")
    if payload.get("ok") is not None and payload.get("ok") not in (True, False):
        errors.append("ok: if present must be bool")
    if payload.get("ok") is not None and payload.get("ok") != (payload.get("status") == OK_STATUS):
        errors.append("ok: if present must equal (status == 'ok')")
    if payload.get("route_mode") != "fail-closed":
        errors.append("route_mode: must be 'fail-closed'")
    if payload.get("fail_closed") is not True:
        errors.append("fail_closed: must be true")
    if payload.get("promoted") is not None and payload.get("promoted") is not False:
        errors.append("promoted: if present must be false")

    _check_control_card(payload, errors)
    _check_authority(payload, errors)

    source_dependency = payload.get("source_contract_dependency")
    if source_dependency != SOURCE_CONTRACT_DEPENDENCY:
        errors.append(f"source_contract_dependency: must be {SOURCE_CONTRACT_DEPENDENCY!r}")

    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        errors.append("inputs: must be object")
    else:
        for key in ("raw_archive", "output_json"):
            if not isinstance(inputs.get(key), str) or not inputs.get(key):
                errors.append(f"inputs.{key}: must be non-empty string")

    params = payload.get("parameters")
    if not isinstance(params, dict):
        errors.append("parameters: must be object")
    else:
        for key in ("frame", "frame_limit", "seed"):
            value = params.get(key)
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"parameters.{key}: must be null or nonnegative int")
        if "top_k" in params and _positive_int(params.get("top_k")) is None:
            errors.append("parameters.top_k: must be positive int")
        if "pool_multiplier" in params and _positive_int(params.get("pool_multiplier")) is None:
            errors.append("parameters.pool_multiplier: must be positive int")
        if "seed" in params and _nonnegative_int(params.get("seed")) is None:
            errors.append("parameters.seed: must be nonnegative int")
        zero_eps = _finite_float(params.get("zero_eps"))
        if zero_eps is None or zero_eps <= 0.0:
            errors.append("parameters.zero_eps: must be finite positive")
        if _finite_float(params.get("gamma")) is None:
            errors.append("parameters.gamma: must be finite")
        if _finite_float(params.get("condition_threshold")) is None:
            errors.append("parameters.condition_threshold: must be finite")
        if _finite_float(params.get("support_eps")) is None or _finite_float(params.get("support_eps")) < 0.0:
            errors.append("parameters.support_eps: must be finite nonnegative")
        if _finite_float(params.get("overlap_tol")) is None or _finite_float(params.get("overlap_tol")) < 0.0:
            errors.append("parameters.overlap_tol: must be finite nonnegative")
        shells = params.get("shells")
        if shells is not None:
            if not isinstance(shells, list) or not shells:
                errors.append("parameters.shells: must be non-empty list or null")
            else:
                for index, shell in enumerate(shells):
                    if _positive_int(shell) is None:
                        errors.append(f"parameters.shells[{index}]: must be positive int")

    rows = payload.get("triad_cycle_packing_overlap_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("triad_cycle_packing_overlap_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"triad_cycle_packing_overlap_rows[{index}]: must be object")
            continue
        _check_row(row, f"triad_cycle_packing_overlap_rows[{index}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    _check_aggregate(aggregate, rows, errors)

    if not isinstance(payload.get("warnings"), list):
        errors.append("warnings: must be list")
    if not isinstance(payload.get("errors"), list):
        errors.append("errors: must be list")

    return errors


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(_input_path(args))
        errors = _check_payload(payload)
    except Exception as exc:  # noqa: BLE001
        errors = [str(exc)]

    receipt = {
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script_name": SCRIPT_NAME,
        "source_json": str(_input_path(args)),
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "error_count": int(len(errors)),
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
