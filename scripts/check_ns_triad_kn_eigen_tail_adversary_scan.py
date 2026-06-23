#!/usr/bin/env python3
"""Validate ns_triad_kn_eigen_tail_adversary_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_kn_eigen_tail_adversary_scan.py"
CONTRACT = "check_ns_triad_kn_eigen_tail_adversary_scan"
SOURCE_CONTRACT = "ns_triad_kn_eigen_tail_adversary_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_kn_eigen_tail_adversary_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EIGEN_TAIL_ADVERSARY_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EIGEN_TAIL_ADVERSARY_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

ALLOWED_TAIL_BRANCHES = {
    "frame-coercive",
    "tail-escape",
    "tail-loaded",
    "eigenvector-tail-escape",
    "tail-contained",
}

EXPECTED_AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}

EXPECTED_CONTROL_CARD = {
    "O": "Run a focused adversary scan that pushes K_N(A) profile tails upward and ranks the low-lambda survivors.",
    "R": (
        "Use the existing candidate-profile generator and iterative generalized eigen evaluator, "
        "bias profiles toward high-shell mass, and classify whether the worst eigenvector escapes "
        "into the tail region."
    ),
    "C": SOURCE_SCRIPT_NAME,
    "S": "Candidate-only telemetry; no theorem, full-NS, or Clay promotion is inferred.",
    "L": (
        "Load shell carriers, build tail-biased amplitude profiles, solve L_neg x = lambda L_abs x "
        "with CPU or Vulkan matvecs, and report the lowest lambda candidates together with tail-escape labels."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "GPU matvecs remain non-authoritative and gpu_kn_authority is always false.",
    "F": "This is a focused empirical adversary scan; it does not prove any asymptotic tail exclusion.",
}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_eigen_tail_adversary_scan_N128_20260623.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_kn_eigen_tail_adversary_scan_N128_20260623.json"
)


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


def _finite(value: Any) -> float | None:
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
    if isinstance(value, int) and value >= 0:
        return value
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _validate_expected_flags(payload: dict[str, Any], field_name: str, expected: dict[str, bool], errors: list[str]) -> None:
    field = payload.get(field_name)
    if not isinstance(field, dict):
        errors.append(f"{field_name}: must be object")
        return
    for key, expected_value in expected.items():
        if field.get(key) is not expected_value:
            errors.append(f"{field_name}.{key}: must be {expected_value!r}")


def _validate_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    control_card = payload.get("control_card")
    if not isinstance(control_card, dict):
        errors.append("control_card: must be object")
        return
    for key, expected_value in EXPECTED_CONTROL_CARD.items():
        if control_card.get(key) != expected_value:
            errors.append(f"control_card.{key}: must be {expected_value!r}")


def _validate_tail_branch(value: Any, path: str, errors: list[str]) -> None:
    if value not in ALLOWED_TAIL_BRANCHES:
        errors.append(f"{path}: invalid tail branch")


def _validate_tail_grid(tail_grid: Any, path: str, errors: list[str]) -> None:
    if not isinstance(tail_grid, list):
        errors.append(f"{path}: must be list")
        return
    for index, item in enumerate(tail_grid):
        if not isinstance(item, dict):
            errors.append(f"{path}[{index}]: must be object")
            continue
        for key in ("c0", "tail_eta", "high_shell_mass_k"):
            if _finite(item.get(key)) is None:
                errors.append(f"{path}[{index}].{key}: must be finite")
        if item.get("eigen_tail_mass_k") is not None and _finite(item.get("eigen_tail_mass_k")) is None:
            errors.append(f"{path}[{index}].eigen_tail_mass_k: must be finite or null")
        if item.get("eigen_tail_high") is not None and not isinstance(item.get("eigen_tail_high"), bool):
            errors.append(f"{path}[{index}].eigen_tail_high: must be bool or null")
        if _nonnegative_int(item.get("tail_cutoff")) is None:
            errors.append(f"{path}[{index}].tail_cutoff: must be nonnegative int")
        _validate_tail_branch(item.get("branch"), f"{path}[{index}].branch", errors)


def _validate_tail_grid_summary(summary: Any, path: str, errors: list[str]) -> None:
    if not isinstance(summary, dict):
        errors.append(f"{path}: must be object")
        return
    for key in ("grid_point_count", "frame_coercive_count", "tail_escape_count", "tail_loaded_count", "tail_contained_count", "eigenvector_tail_escape_count"):
        if _nonnegative_int(summary.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int")
    branch_counts = summary.get("branch_counts")
    if not isinstance(branch_counts, dict):
        errors.append(f"{path}.branch_counts: must be object")
    else:
        for key, value in branch_counts.items():
            if key not in ALLOWED_TAIL_BRANCHES:
                errors.append(f"{path}.branch_counts.{key}: invalid tail branch")
            if _nonnegative_int(value) is None:
                errors.append(f"{path}.branch_counts.{key}: must be nonnegative int")


def _validate_metrics(metrics: Any, path: str, errors: list[str]) -> None:
    if not isinstance(metrics, dict):
        errors.append(f"{path}: must be object")
        return
    for key in (
        "angular_entropy",
        "angular_mode_count",
        "bkm_proxy",
        "dissipation_proxy",
        "energy",
        "high_shell_mass_fraction",
        "n_eff",
        "radial_effective_scale",
        "radial_shell_barycenter",
        "radial_shell_max",
        "radial_shell_min",
        "radial_shell_variance",
    ):
        if _finite(metrics.get(key)) is None:
            errors.append(f"{path}.{key}: must be finite")
    high_shell_mass_by_cutoff = metrics.get("high_shell_mass_by_cutoff")
    if not isinstance(high_shell_mass_by_cutoff, dict):
        errors.append(f"{path}.high_shell_mass_by_cutoff: must be object")
    else:
        for cutoff, value in high_shell_mass_by_cutoff.items():
            if _finite(value) is None:
                errors.append(f"{path}.high_shell_mass_by_cutoff.{cutoff}: must be finite")
    radial_shell_max_with_mass_eta = metrics.get("radial_shell_max_with_mass_eta")
    if not isinstance(radial_shell_max_with_mass_eta, dict):
        errors.append(f"{path}.radial_shell_max_with_mass_eta: must be object")
    else:
        for eta_key, value in radial_shell_max_with_mass_eta.items():
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"{path}.radial_shell_max_with_mass_eta.{eta_key}: must be nonnegative int or null")
    eigen_tail_mass_by_cutoff = metrics.get("eigen_tail_mass_by_cutoff")
    if not isinstance(eigen_tail_mass_by_cutoff, dict):
        errors.append(f"{path}.eigen_tail_mass_by_cutoff: must be object")
    else:
        for cutoff, value in eigen_tail_mass_by_cutoff.items():
            if value is not None and _finite(value) is None:
                errors.append(f"{path}.eigen_tail_mass_by_cutoff.{cutoff}: must be finite or null")
    for key in ("eigen_shell_barycenter", "eigen_shell_variance"):
        if metrics.get(key) is not None and _finite(metrics.get(key)) is None:
            errors.append(f"{path}.{key}: must be finite or null")
    eigen_shell_max_with_mass_eta = metrics.get("eigen_shell_max_with_mass_eta")
    if not isinstance(eigen_shell_max_with_mass_eta, dict):
        errors.append(f"{path}.eigen_shell_max_with_mass_eta: must be object")
    else:
        for eta_key, value in eigen_shell_max_with_mass_eta.items():
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"{path}.eigen_shell_max_with_mass_eta.{eta_key}: must be nonnegative int or null")


def _validate_candidate_profile(profile: Any, path: str, backend: str, errors: list[str]) -> None:
    if profile is None:
        return
    if not isinstance(profile, dict):
        errors.append(f"{path}: must be object or null")
        return

    if profile.get("profile_id") is not None and (not isinstance(profile.get("profile_id"), str) or not profile.get("profile_id")):
        errors.append(f"{path}.profile_id: must be non-empty string or null")
    if profile.get("status") not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: invalid")
    if profile.get("kn_backend") != backend:
        errors.append(f"{path}.kn_backend: must match parameters.kn_backend")
    if profile.get("parity_ok") not in (True, False):
        errors.append(f"{path}.parity_ok: must be bool")
    if profile.get("dense_oracle_used") not in (True, False):
        errors.append(f"{path}.dense_oracle_used: must be bool")
    for key in ("candidate_only", "fail_closed"):
        if profile.get(key) is not True:
            errors.append(f"{path}.{key}: must be true")
    for key in ("gpu_kn_authority", "theorem_promoted", "full_ns_promoted", "clay_promoted", "dense_reconstruction_used"):
        if profile.get(key) is not False:
            errors.append(f"{path}.{key}: must be false")

    if profile.get("block_matvec_enabled") not in (True, False):
        errors.append(f"{path}.block_matvec_enabled: must be bool")
    if profile.get("block_matvec_backend") is not None and not isinstance(profile.get("block_matvec_backend"), str):
        errors.append(f"{path}.block_matvec_backend: must be string or null")
    if profile.get("vulkan_icd") is not None and not isinstance(profile.get("vulkan_icd"), str):
        errors.append(f"{path}.vulkan_icd: must be string or null")

    for key in (
        "lambda_min_dense_cpu",
        "lambda_min_iterative",
        "lambda_rank",
        "relative_error_vs_dense",
        "worst_eigenvector_shell_iterative",
        "worst_eigenvector_shell_mass_iterative",
        "iterations",
        "residual_norm",
        "elapsed_ms",
    ):
        value = profile.get(key)
        if value is not None and _finite(value) is None:
            errors.append(f"{path}.{key}: must be finite or null")

    if profile.get("dense_oracle_used") is True:
        for key in ("lambda_min_dense_cpu", "relative_error_vs_dense"):
            if _finite(profile.get(key)) is None:
                errors.append(f"{path}.{key}: must be finite when dense oracle is used")

    _validate_metrics(profile.get("metrics"), f"{path}.metrics", errors)
    _validate_tail_grid_summary(profile.get("tail_grid_summary"), f"{path}.tail_grid_summary", errors)
    _validate_tail_grid(profile.get("tail_grid"), f"{path}.tail_grid", errors)

    warnings = profile.get("warnings")
    if warnings is not None and not isinstance(warnings, list):
        errors.append(f"{path}.warnings: must be list or null")


def _validate_parameters(payload: dict[str, Any], errors: list[str]) -> dict[str, Any]:
    parameters = payload.get("parameters")
    if not isinstance(parameters, dict):
        errors.append("parameters: must be object")
        return {}

    if not isinstance(parameters.get("raw_archive"), str) or not parameters.get("raw_archive"):
        errors.append("parameters.raw_archive: must be non-empty string")
    if not isinstance(parameters.get("output_json"), str) or not parameters.get("output_json"):
        errors.append("parameters.output_json: must be non-empty string")
    if parameters.get("kn_backend") not in {"cpu-matrix-free", "vulkan-matvec"}:
        errors.append("parameters.kn_backend: invalid")

    if parameters.get("frame") is not None and _nonnegative_int(parameters.get("frame")) is None:
        errors.append("parameters.frame: must be nonnegative int or null")
    for key in ("frame_limit", "sample_count", "mix_count", "lobpcg_maxiter", "block_size", "dense_oracle_shell_limit", "gpu_matvec_checks", "profile_sample_limit", "max_profiles_per_row"):
        if _nonnegative_int(parameters.get(key)) is None:
            errors.append(f"parameters.{key}: must be nonnegative int")
    if _finite(parameters.get("zero_eps")) is None:
        errors.append("parameters.zero_eps: must be finite")
    for key in ("r0", "d0", "parity_tol", "lobpcg_tol", "generalized_mass_shift"):
        if _finite(parameters.get(key)) is None:
            errors.append(f"parameters.{key}: must be finite")

    for key in ("seeds", "shells", "c0_values", "tail_cutoffs", "tail_etas"):
        value = parameters.get(key)
        if not isinstance(value, list) or not value:
            errors.append(f"parameters.{key}: must be non-empty list")
    if isinstance(parameters.get("shells"), list):
        for index, shell in enumerate(parameters["shells"]):
            if _nonnegative_int(shell) is None:
                errors.append(f"parameters.shells[{index}]: must be nonnegative int")
    if isinstance(parameters.get("tail_cutoffs"), list):
        for index, cutoff in enumerate(parameters["tail_cutoffs"]):
            if _nonnegative_int(cutoff) is None:
                errors.append(f"parameters.tail_cutoffs[{index}]: must be nonnegative int")
    if isinstance(parameters.get("seeds"), list):
        for index, seed in enumerate(parameters["seeds"]):
            if _nonnegative_int(seed) is None:
                errors.append(f"parameters.seeds[{index}]: must be nonnegative int")
    for key in ("c0_values", "tail_etas"):
        if isinstance(parameters.get(key), list):
            for index, value in enumerate(parameters[key]):
                if _finite(value) is None:
                    errors.append(f"parameters.{key}[{index}]: must be finite")

    if not isinstance(parameters.get("force_tail_profiles"), bool):
        errors.append("parameters.force_tail_profiles: must be bool")
    return parameters


def _validate_row(row: dict[str, Any], index: int, parameters: dict[str, Any], errors: list[str]) -> None:
    if row.get("status") not in ALLOWED_STATUSES:
        errors.append(f"rows[{index}].status: invalid")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"rows[{index}].frame: must be nonnegative int")
    if _nonnegative_int(row.get("snapshot_index")) is None:
        errors.append(f"rows[{index}].snapshot_index: must be nonnegative int")
    if _nonnegative_int(row.get("shell")) is None:
        errors.append(f"rows[{index}].shell: must be nonnegative int")
    for key in (
        "candidate_only",
        "fail_closed",
        "tail_biased_scan",
    ):
        if row.get(key) is not True:
            errors.append(f"rows[{index}].{key}: must be true")
    for key in ("gpu_kn_authority", "theorem_promoted", "full_ns_promoted", "clay_promoted", "dense_reconstruction_used"):
        if row.get(key) is not False:
            errors.append(f"rows[{index}].{key}: must be false")
    if row.get("kn_backend") != parameters.get("kn_backend"):
        errors.append(f"rows[{index}].kn_backend: must match parameters.kn_backend")
    if row.get("dense_oracle_used") not in (True, False):
        errors.append(f"rows[{index}].dense_oracle_used: must be bool")
    if row.get("block_matvec_enabled") is not None and row.get("block_matvec_enabled") not in (True, False):
        errors.append(f"rows[{index}].block_matvec_enabled: must be bool when present")
    for key in ("block_matvec_backend", "vulkan_icd"):
        if row.get(key) is not None and not isinstance(row.get(key), str):
            errors.append(f"rows[{index}].{key}: must be string or null")

    for key in (
        "selected_mode_count",
        "triad_count",
        "carrier_stratum_count",
        "profile_count",
        "candidate_receipt_count",
        "parity_ok_count",
        "parity_mismatch_count",
        "tail_escape_candidate_count",
    ):
        if _nonnegative_int(row.get(key)) is None:
            errors.append(f"rows[{index}].{key}: must be nonnegative int")

    for key in ("best_low_lambda_profile", "best_tail_escape_profile"):
        _validate_candidate_profile(row.get(key), f"rows[{index}].{key}", str(parameters.get("kn_backend")), errors)

    candidate_receipts = row.get("candidate_receipts")
    if not isinstance(candidate_receipts, list):
        errors.append(f"rows[{index}].candidate_receipts: must be list")
    else:
        if _nonnegative_int(row.get("candidate_receipt_count")) is not None and row.get("candidate_receipt_count") < len(candidate_receipts):
            errors.append(f"rows[{index}].candidate_receipt_count: cannot be less than emitted candidate_receipts length")
        if _nonnegative_int(row.get("profile_count")) is not None and row.get("profile_count") < len(candidate_receipts):
            errors.append(f"rows[{index}].profile_count: cannot be less than emitted candidate_receipts length")
        if _nonnegative_int(row.get("parity_ok_count")) is not None and _nonnegative_int(row.get("parity_mismatch_count")) is not None:
            expected_count = int(row.get("candidate_receipt_count", len(candidate_receipts)))
            if int(row["parity_ok_count"]) + int(row["parity_mismatch_count"]) != expected_count:
                errors.append(f"rows[{index}].parity_ok_count/parity_mismatch_count: must sum to candidate_receipt_count")
        if _nonnegative_int(row.get("tail_escape_candidate_count")) is not None and _nonnegative_int(row.get("candidate_receipt_count")) is not None:
            if int(row["tail_escape_candidate_count"]) > int(row["candidate_receipt_count"]):
                errors.append(f"rows[{index}].tail_escape_candidate_count: cannot exceed candidate_receipt_count")
        for sample_index, candidate in enumerate(candidate_receipts):
            _validate_candidate_profile(candidate, f"rows[{index}].candidate_receipts[{sample_index}]", str(parameters.get("kn_backend")), errors)

    warnings = row.get("warnings")
    if warnings is not None and not isinstance(warnings, list):
        errors.append(f"rows[{index}].warnings: must be list or null")
    row_errors = row.get("errors")
    if row_errors is not None and not isinstance(row_errors, list):
        errors.append(f"rows[{index}].errors: must be list or null")


def _validate_aggregate(aggregate: Any, rows: list[dict[str, Any]], parameters: dict[str, Any], errors: list[str]) -> None:
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        return

    for key in ("processed_rows", "ok_rows", "partial_rows", "error_rows", "candidate_receipt_count", "parity_mismatch_count", "tail_escape_candidate_count"):
        if _nonnegative_int(aggregate.get(key)) is None:
            errors.append(f"aggregate.{key}: must be nonnegative int")
    if _nonnegative_int(aggregate.get("processed_rows")) is not None and aggregate.get("processed_rows") != len(rows):
        errors.append("aggregate.processed_rows: must match row count")
    if _nonnegative_int(aggregate.get("ok_rows")) is not None and aggregate.get("ok_rows") != sum(1 for row in rows if row.get("status") == OK_STATUS):
        errors.append("aggregate.ok_rows: must match row count")
    if _nonnegative_int(aggregate.get("partial_rows")) is not None and aggregate.get("partial_rows") != sum(1 for row in rows if row.get("status") == PARTIAL_STATUS):
        errors.append("aggregate.partial_rows: must match row count")
    if _nonnegative_int(aggregate.get("error_rows")) is not None and aggregate.get("error_rows") != sum(1 for row in rows if row.get("status") == ERROR_STATUS):
        errors.append("aggregate.error_rows: must match row count")

    if aggregate.get("kn_backend") != parameters.get("kn_backend"):
        errors.append("aggregate.kn_backend: must match parameters.kn_backend")
    for key in ("candidate_only", "fail_closed"):
        if aggregate.get(key) is not True:
            errors.append(f"aggregate.{key}: must be true")
    for key in ("gpu_kn_authority", "theorem_promoted", "full_ns_promoted", "clay_promoted", "dense_reconstruction_used_by_iterative_lane"):
        if aggregate.get(key) is not False:
            errors.append(f"aggregate.{key}: must be false")
    if aggregate.get("dense_eigensolve_scope") != "small_shell_oracle_only":
        errors.append("aggregate.dense_eigensolve_scope: must be 'small_shell_oracle_only'")
    if aggregate.get("tail_adversary_status") not in {"candidate-tail-telemetry", "fail-closed"}:
        errors.append("aggregate.tail_adversary_status: invalid")

    _validate_candidate_profile(aggregate.get("best_global_low_lambda_profile"), "aggregate.best_global_low_lambda_profile", str(parameters.get("kn_backend")), errors)

    best_profile_worst_shells = aggregate.get("best_profile_worst_shells")
    if not isinstance(best_profile_worst_shells, list):
        errors.append("aggregate.best_profile_worst_shells: must be list")
    else:
        for index, value in enumerate(best_profile_worst_shells):
            if _nonnegative_int(value) is None:
                errors.append(f"aggregate.best_profile_worst_shells[{index}]: must be nonnegative int")
    if aggregate.get("worst_shell_progression_max") is not None and _nonnegative_int(aggregate.get("worst_shell_progression_max")) is None:
        errors.append("aggregate.worst_shell_progression_max: must be nonnegative int or null")

    warnings = aggregate.get("warnings")
    if warnings is not None and not isinstance(warnings, list):
        errors.append("aggregate.warnings: must be list or null")


def main() -> int:
    args = _parse_args()
    source_json = _input_path(args)
    try:
        payload = _load_json(source_json)
    except Exception as exc:  # noqa: BLE001
        result = {
            "script_name": SCRIPT_NAME,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "source_json": str(source_json),
            "source_contract": SOURCE_CONTRACT,
            "source_script_name": SOURCE_SCRIPT_NAME,
            "status": ERROR_STATUS,
            "ok": False,
            "error_count": 1,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(result, args.pretty))
        return 1

    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")

    _validate_expected_flags(payload, "authority", EXPECTED_AUTHORITY, errors)
    _validate_control_card(payload, errors)

    parameters = _validate_parameters(payload, errors)

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        errors.append("rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"rows[{index}]: must be object")
            continue
        _validate_row(row, index, parameters, errors)

    _validate_aggregate(payload.get("aggregate"), rows, parameters, errors)

    warnings = payload.get("warnings")
    if warnings is not None and not isinstance(warnings, list):
        errors.append("warnings: must be list or null")
    top_errors = payload.get("errors")
    if top_errors is not None and not isinstance(top_errors, list):
        errors.append("errors: must be list or null")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append("status: must be ok|partial|error")

    receipt = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "source_json": str(source_json),
        "source_contract": SOURCE_CONTRACT,
        "source_script_name": SOURCE_SCRIPT_NAME,
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
