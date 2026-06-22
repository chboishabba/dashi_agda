#!/usr/bin/env python3
"""Validate ns_triad_k01_geometry_audit_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_k01_geometry_audit_scan.py"
CONTRACT = "check_ns_triad_k01_geometry_audit_scan"
SOURCE_CONTRACT = "ns_triad_k01_geometry_audit_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_k01_geometry_audit_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_K01_GEOMETRY_AUDIT_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_K01_GEOMETRY_AUDIT_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"
ALLOWED_SOURCE_STATUSES = {"ok", "partial", "error"}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_k01_geometry_audit_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_k01_geometry_audit_scan_N128_20260621.json"
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

REQUIRED_ROW_KEYS = {
    "frame",
    "shell",
    "snapshot_index",
    "source",
    "route_mode",
    "candidate_only",
    "empirical_non_promoting",
    "fail_closed",
    "wall1_status",
    "wall1_proved",
    "status",
}

OPTIONAL_FINITE_NONNEGATIVE_ROW_KEYS = {
    "selected_mode_count",
    "triad_count",
    "carrier_stratum_count",
    "low_block_size",
    "high_block_size",
    "shell_ratio",
    "shell_fraction",
    "shell_imbalance",
    "shell_curvature_proxy",
    "k00_lambda_max",
    "k01_operator_norm",
    "k11_lambda_max",
    "k01_geometry_ratio",
    "k01_ratio_proxy",
    "k01_to_k00_ratio",
    "k01_to_k11_ratio",
    "off_diagonal_vs_diagonal_ratio",
    "off_diagonal_share_proxy",
    "off_diagonal_contrast_proxy",
    "off_diagonal_pressure_proxy",
    "directional_off_diagonal_pressure_proxy",
    "angular_mismatch_proxy",
    "frame_geometry_proxy",
    "incompressibility_proxy",
    "projection_proxy",
    "directional_gap_proxy",
    "directional_gap_lower_bound",
    "directional_gap_residual",
    "directional_gap_ratio",
    "directional_gap_residual_ratio",
    "geometry_stability_proxy",
    "geometry_alignment_proxy",
    "coupling_concentration",
    "dangerous_subspace_weight_fraction",
    "frame_stability_margin_proxy",
    "positive_backbone_operator_gap_proxy",
    "negative_frame_operator_gap_proxy",
    "combined_operator_gap_proxy",
    "frame_stability_proxy",
    "selected_mode_amplitude_sum",
    "mode_concentration_fraction",
    "carrier_shell_radius_mean",
    "carrier_shell_radius_p95",
    "backbone_vs_negative_gap_ratio",
    "stratum_cross_mass_ratio",
    "stratum_internal_mass_ratio",
    "stratum_balance_entropy_normalized",
    "triad_phase_coherence_abs_mean",
    "triad_shell_spread_mean",
    "triad_shell_spread_p95",
    "geometry_completeness",
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


def _check_fraction(errors: list[str], path: str, value: Any) -> None:
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        errors.append(f"{path}: must be finite fraction in [0,1]")


def _check_authority(authority: Any, errors: list[str]) -> None:
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
        return
    for key, expected in EXPECTED_AUTHORITY.items():
        if authority.get(key) is not expected:
            errors.append(f"authority.{key}: must be {expected!r}")


def _check_row(row: dict[str, Any], index: int, errors: list[str]) -> None:
    path = f"rows[{index}]"
    missing = sorted(REQUIRED_ROW_KEYS - set(row))
    if missing:
        errors.append(f"{path}: missing required keys {missing}")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    if _nonnegative_int(row.get("shell")) is None:
        errors.append(f"{path}.shell: must be nonnegative int")
    if _nonnegative_int(row.get("snapshot_index")) is None:
        errors.append(f"{path}.snapshot_index: must be nonnegative int")
    if not isinstance(row.get("source"), str) or not row.get("source"):
        errors.append(f"{path}.source: must be non-empty string")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    if row.get("candidate_only") is not True:
        errors.append(f"{path}.candidate_only: must be true")
    if row.get("empirical_non_promoting") is not True:
        errors.append(f"{path}.empirical_non_promoting: must be true")
    if row.get("fail_closed") is not True:
        errors.append(f"{path}.fail_closed: must be true")
    if row.get("wall1_status") != "unproved":
        errors.append(f"{path}.wall1_status: must be 'unproved'")
    if row.get("wall1_proved") is not False:
        errors.append(f"{path}.wall1_proved: must be false")
    if row.get("status") not in ALLOWED_SOURCE_STATUSES:
        errors.append(f"{path}.status: must be one of {sorted(ALLOWED_SOURCE_STATUSES)!r}")
    if row.get("warnings") is not None and not isinstance(row.get("warnings"), list):
        errors.append(f"{path}.warnings: must be list or null")
    if row.get("errors") is not None and not isinstance(row.get("errors"), list):
        errors.append(f"{path}.errors: must be list or null")

    if row.get("dangerous_shell_is_high") not in (True, False):
        errors.append(f"{path}.dangerous_shell_is_high: must be bool")
    if not isinstance(row.get("dangerous_shell_partition"), str) or not row.get("dangerous_shell_partition"):
        errors.append(f"{path}.dangerous_shell_partition: must be non-empty string")

    for key in OPTIONAL_FINITE_NONNEGATIVE_ROW_KEYS:
        value = row.get(key)
        if value is None:
            continue
        parsed = _finite_float(value)
        if parsed is None or parsed < -1.0e-12:
            errors.append(f"{path}.{key}: must be finite nonnegative or null")

    for key in (
        "shell_fraction",
        "shell_imbalance",
        "k01_geometry_ratio",
        "k01_ratio_proxy",
        "k01_to_k00_ratio",
        "k01_to_k11_ratio",
        "off_diagonal_vs_diagonal_ratio",
        "off_diagonal_share_proxy",
        "off_diagonal_contrast_proxy",
        "off_diagonal_pressure_proxy",
        "directional_gap_ratio",
        "directional_gap_residual_ratio",
        "geometry_alignment_proxy",
        "coupling_concentration",
        "dangerous_subspace_weight_fraction",
        "mode_concentration_fraction",
        "stratum_cross_mass_ratio",
        "stratum_internal_mass_ratio",
        "stratum_balance_entropy_normalized",
        "triad_phase_coherence_abs_mean",
        "geometry_completeness",
    ):
        value = row.get(key)
        if value is not None:
            _check_fraction(errors, f"{path}.{key}", value)

    coherence = _finite_float(row.get("triad_phase_coherence_mean"))
    if coherence is not None and (coherence < -1.0 - 1.0e-12 or coherence > 1.0 + 1.0e-12):
        errors.append(f"{path}.triad_phase_coherence_mean: must lie in [-1,1] when present")


def _check_aggregate(aggregate: Any, row_count: int, errors: list[str]) -> None:
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        return
    for key in ("processed_rows", "ok_rows", "partial_rows", "error_rows", "shared_frame_count", "shared_frame_shell_count", "shared_shell_count"):
        if _nonnegative_int(aggregate.get(key)) is None:
            errors.append(f"aggregate.{key}: must be nonnegative int")
    processed_rows = _nonnegative_int(aggregate.get("processed_rows")) or 0
    if processed_rows != row_count:
        errors.append("aggregate.processed_rows: must match row count")
    counts = [_nonnegative_int(aggregate.get(key)) or 0 for key in ("ok_rows", "partial_rows", "error_rows")]
    if sum(counts) != processed_rows:
        errors.append("aggregate row status counts must sum to processed_rows")
    if aggregate.get("wall1_status") != "unproved":
        errors.append("aggregate.wall1_status: must be 'unproved'")
    if aggregate.get("candidate_only") is not True:
        errors.append("aggregate.candidate_only: must be true")
    if aggregate.get("empirical_non_promoting") is not True:
        errors.append("aggregate.empirical_non_promoting: must be true")
    if aggregate.get("fail_closed") is not True:
        errors.append("aggregate.fail_closed: must be true")
    if aggregate.get("theorem_authority") is not False:
        errors.append("aggregate.theorem_authority: must be false")
    if aggregate.get("clay_authority") is not False:
        errors.append("aggregate.clay_authority: must be false")
    if aggregate.get("geometry_sufficiency_counts") is not None and not isinstance(aggregate.get("geometry_sufficiency_counts"), dict):
        errors.append("aggregate.geometry_sufficiency_counts: must be object or null")

    for key, value in aggregate.items():
        if key in {
            "processed_rows",
            "ok_rows",
            "partial_rows",
            "error_rows",
            "shared_frame_count",
            "shared_frame_shell_count",
            "shared_shell_count",
            "present_surface_count",
            "source_surface_count",
            "wall1_status",
            "wall1_proved",
            "candidate_only",
            "empirical_non_promoting",
            "fail_closed",
            "theorem_authority",
            "clay_authority",
            "geometry_sufficiency_counts",
        }:
            continue
        if value is None:
            continue
        if key.endswith("_correlation"):
            parsed = _finite_float(value)
            if parsed is None or parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12:
                errors.append(f"aggregate.{key}: must be finite in [-1,1] or null")
            continue
        parsed = _finite_float(value)
        if parsed is None or parsed < -1.0e-12:
            errors.append(f"aggregate.{key}: must be finite nonnegative or null")


def main() -> int:
    args = _parse_args()
    source_json = _input_path(args)
    payload = _load_json(source_json)
    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("status") not in ALLOWED_SOURCE_STATUSES:
        errors.append(f"status: must be one of {sorted(ALLOWED_SOURCE_STATUSES)!r}")
    if payload.get("candidate_only") is not True:
        errors.append("candidate_only: must be true")
    if payload.get("empirical_non_promoting") is not True:
        errors.append("empirical_non_promoting: must be true")
    if payload.get("fail_closed") is not True:
        errors.append("fail_closed: must be true")
    if payload.get("wall1_status") != "unproved":
        errors.append("wall1_status: must be 'unproved'")
    if payload.get("wall1_proved") is not False:
        errors.append("wall1_proved: must be false")

    _check_authority(payload.get("authority"), errors)

    rows = payload.get("rows")
    if not isinstance(rows, list):
        errors.append("rows: must be list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"rows[{index}]: must be object")
            continue
        _check_row(row, index, errors)

    _check_aggregate(payload.get("aggregate"), len(rows), errors)

    status = OK_STATUS if not errors else ERROR_STATUS
    receipt = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "source_json": str(source_json),
        "status": status,
        "ok": status == OK_STATUS,
        "error_count": int(len(errors)),
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
