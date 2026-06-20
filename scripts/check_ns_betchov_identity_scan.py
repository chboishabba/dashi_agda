#!/usr/bin/env python3
"""Validate ns_betchov_identity_scan outputs."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_betchov_identity_scan.py"
CONTRACT = "check_ns_betchov_identity_scan"
SCAN_CONTRACT = "ns_betchov_identity_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_BETCHOV_IDENTITY_SCAN"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"

ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}

DEFAULT_INPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_betchov_identity_scan_N128_20260620.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_betchov_identity_scan_N128_20260620.json"
)

CONTROL_CARD = {
    "O": "Validate the Betchov identity scan contract.",
    "R": "Fail-closed check of frame payload, aggregate bookkeeping, and authority fields for raw-archive reconstruction outputs.",
    "C": SCRIPT_NAME,
    "S": "Schema violations, non-finite non-optional quantities, residual mismatches, or aggregate-count inconsistency are hard errors.",
    "L": "Read scan JSON, validate control card/authority, verify row-level and aggregate-level invariants.",
    "P": "FAIL_CLOSED_BETCHOV_IDENTITY_SCAN_CHECK",
    "G": "This checker only validates empirical telemetry and does not promote theorem/Clay claims.",
    "F": "Partial rows, missing quantities, and finite-cell degradation are accepted only when explicitly declared.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-json", type=Path, default=DEFAULT_INPUT, help="Path to ns_betchov_identity_scan output")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT, help="Path for checker output")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"scan JSON missing: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"scan JSON must be an object: {path}")
    return payload


def _coerce_finite_float(value: Any, *, name: str, warnings: list[str], errors: list[str], path: str) -> float | None:
    if value is None or isinstance(value, bool):
        errors.append(f"{path}:{name} missing or non-numeric")
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        errors.append(f"{path}:{name} not parseable as float: {value!r}")
        return None
    if not math.isfinite(parsed):
        errors.append(f"{path}:{name} not finite: {value!r}")
        return None
    return parsed


def _coerce_nonnegative_int(value: Any, path: str, key: str, errors: list[str]) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{path}:{key} must be non-negative int, got {type(value).__name__}")
        return None
    if value < 0:
        errors.append(f"{path}:{key} must be non-negative")
        return None
    return value


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            errors.append(f"control card missing or empty '{key}'")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority missing or not a dictionary")
        return
    expected = {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }
    for key, required in expected.items():
        value = authority.get(key)
        if not isinstance(value, bool):
            errors.append(f"authority.{key} must be bool")
        elif value is not required:
            errors.append(f"authority.{key} must be {required}")


def _validate_input(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> None:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        errors.append("inputs must be a dictionary")
        return
    raw_archive = inputs.get("raw_archive")
    if not isinstance(raw_archive, str) or not raw_archive.strip():
        errors.append("inputs.raw_archive missing")
    frame = inputs.get("frame")
    if frame is not None and (not isinstance(frame, int) or frame < 0):
        errors.append("inputs.frame must be non-negative int or null")
    frame_limit = inputs.get("frame_limit")
    if frame_limit is not None:
        if not isinstance(frame_limit, int) or frame_limit <= 0:
            errors.append("inputs.frame_limit must be positive int or null")

    if inputs.get("domain_length") is not None and not isinstance(inputs.get("domain_length"), (int, float)):
        errors.append("inputs.domain_length must be numeric")


def _check_rows(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> list[dict[str, Any]]:
    rows = payload.get("rows")
    if not isinstance(rows, list):
        errors.append("rows must be a list")
        return []

    for index, row in enumerate(rows):
        path = f"rows[{index}]"
        if not isinstance(row, dict):
            errors.append(f"{path} must be an object")
            continue

        status = row.get("status")
        if status not in ALLOWED_STATUSES:
            errors.append(f"{path}.status must be in {sorted(ALLOWED_STATUSES)!r}, got {status!r}")

        if status == ERROR_STATUS:
            if not isinstance(row.get("errors"), list):
                errors.append(f"{path}.errors must be a list for error status")
            continue

        frame = _coerce_nonnegative_int(row.get("frame"), path, "frame", errors)
        snapshot = _coerce_nonnegative_int(row.get("snapshot_index"), path, "snapshot_index", errors)
        _ = _coerce_nonnegative_int(row.get("cell_count"), path, "cell_count", errors)
        _ = _coerce_nonnegative_int(row.get("valid_cell_count"), path, "valid_cell_count", errors)
        if frame is None or snapshot is None:
            continue

        if status == MISSING_REQUIRED_STATUS:
            if "errors" not in row or not isinstance(row.get("errors"), list):
                errors.append(f"{path}.errors must be list when status is missing_required_field")
            continue

        det = _coerce_finite_float(row.get("integral_detS"), name="integral_detS", warnings=warnings, errors=errors, path=path)
        pi = _coerce_finite_float(row.get("integral_pi"), name="integral_pi", warnings=warnings, errors=errors, path=path)
        residual = _coerce_finite_float(
            row.get("relation_residual"), name="relation_residual", warnings=warnings, errors=errors, path=path
        )
        _ = _coerce_finite_float(
            row.get("relation_residual_abs"),
            name="relation_residual_abs",
            warnings=warnings,
            errors=errors,
            path=path,
        )
        _ = _coerce_finite_float(
            row.get("relation_residual_relative"),
            name="relation_residual_relative",
            warnings=warnings,
            errors=errors,
            path=path,
        )
        if det is not None and pi is not None and residual is not None:
            expected = det + 0.25 * pi
            if abs(residual - expected) > 1.0e-9:
                warnings.append(f"{path}: relation residual mismatch detS + Pi/4")

        finite_fraction = _coerce_finite_float(
            row.get("finite_fraction"),
            name="finite_fraction",
            warnings=warnings,
            errors=errors,
            path=path,
        )
        if finite_fraction is not None and not (0.0 <= finite_fraction <= 1.0):
            warnings.append(f"{path}.finite_fraction outside [0,1]")

        for key in ("detS_min", "detS_max", "pi_density_min", "pi_density_max"):
            if row.get(key) is not None and not math.isfinite(float(row.get(key))):
                errors.append(f"{path}.{key} not finite")

    return rows


def _validate_aggregate(
    payload: dict[str, Any],
    warnings: list[str],
    errors: list[str],
    rows: list[dict[str, Any]],
) -> None:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate must be an object")
        return

    status_counts = {"ok": 0, "partial": 0, "missing_required_field": 0, "error": 0}
    for row in rows:
        if not isinstance(row, dict):
            status_counts["error"] += 1
            continue
        status = row.get("status")
        if status not in ALLOWED_STATUSES:
            status_counts["error"] += 1
            continue
        status_counts[status] += 1

    if aggregate.get("processed_frames") != len(rows):
        errors.append(
            f"aggregate.processed_frames {aggregate.get('processed_frames')!r} != len(rows) {len(rows)!r}"
        )
    if aggregate.get("ok_frames") != status_counts["ok"]:
        errors.append(
            f"aggregate.ok_frames {aggregate.get('ok_frames')!r} != row ok count {status_counts['ok']!r}"
        )
    if aggregate.get("partial_frames") != status_counts["partial"]:
        errors.append(
            f"aggregate.partial_frames {aggregate.get('partial_frames')!r} != row partial count {status_counts['partial']!r}"
        )
    if aggregate.get("missing_frames") != status_counts["missing_required_field"]:
        errors.append(
            f"aggregate.missing_frames {aggregate.get('missing_frames')!r} != row missing count {status_counts['missing_required_field']!r}"
        )
    if aggregate.get("error_frames") != status_counts["error"]:
        errors.append(
            f"aggregate.error_frames {aggregate.get('error_frames')!r} != row error count {status_counts['error']!r}"
        )

    for key in ("ok_frames", "partial_frames", "missing_frames", "error_frames"):
        value = aggregate.get(key)
        if not isinstance(value, int) or isinstance(value, bool):
            errors.append(f"aggregate.{key} must be int")

    global_det = _coerce_finite_float(aggregate.get("global_integral_detS"), name="global_integral_detS", warnings=warnings, errors=errors, path="aggregate")
    global_pi = _coerce_finite_float(aggregate.get("global_integral_pi"), name="global_integral_pi", warnings=warnings, errors=errors, path="aggregate")
    global_residual = _coerce_finite_float(
        aggregate.get("global_relation_residual"), name="global_relation_residual", warnings=warnings, errors=errors, path="aggregate"
    )
    expected = aggregate.get("global_relation_expected_from_totals")
    if expected is not None and global_det is not None and global_pi is not None:
        expected_val = global_det + 0.25 * global_pi
        parsed_expected = _coerce_finite_float(expected, name="global_relation_expected_from_totals", warnings=warnings, errors=errors, path="aggregate")
        if parsed_expected is not None and abs(parsed_expected - expected_val) > 1.0e-9:
            warnings.append("aggregate global relation expected mismatch")

    if global_det is not None and global_pi is not None and global_residual is not None:
        direct = global_det + 0.25 * global_pi
        if abs(global_residual - direct) > 1.0e-9:
            warnings.append("aggregate relation residual mismatch")

    global_det_rel = _coerce_finite_float(aggregate.get("global_relation_residual_abs"), path="aggregate", name="global_relation_residual_abs", warnings=warnings, errors=errors)
    if global_residual is not None and global_det_rel is not None and abs(global_det_rel - abs(global_residual)) > 1.0e-12:
        warnings.append("global_relation_residual_abs does not match abs(global_relation_residual)")

    for key in (
        "global_cell_count",
        "global_valid_cell_count",
        "global_detS_min",
        "global_detS_max",
        "global_pi_density_min",
        "global_pi_density_max",
    ):
        if key in ("global_cell_count", "global_valid_cell_count"):
            value = aggregate.get(key)
            if not isinstance(value, int) or isinstance(value, bool):
                errors.append(f"aggregate.{key} must be int")
        else:
            if aggregate.get(key) is not None and not math.isfinite(float(aggregate.get(key))):
                errors.append(f"aggregate.{key} must be finite or null")

    if aggregate.get("global_relation_expected_from_totals") is not None:
        expected = _coerce_finite_float(aggregate.get("global_relation_expected_from_totals"), name="global_relation_expected_from_totals", warnings=warnings, errors=errors, path="aggregate")
        if expected is not None and global_det is not None and global_pi is not None:
            if abs(expected - (global_det + 0.25 * global_pi)) > 1.0e-9:
                warnings.append("aggregate global_relation_expected_from_totals inconsistent")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []

    if payload.get("contract") != SCAN_CONTRACT:
        errors.append(f"contract must be {SCAN_CONTRACT!r}")
    if payload.get("route_decision") != SCAN_ROUTE_DECISION:
        errors.append(f"route_decision must be {SCAN_ROUTE_DECISION!r}")

    _check_control_card(payload, errors)
    _check_authority(payload, errors)
    _validate_input(payload, warnings, errors)
    rows = _check_rows(payload, warnings, errors)
    _validate_aggregate(payload, warnings, errors, rows)

    if "status" in payload and payload.get("status") not in ALLOWED_STATUSES:
        errors.append(f"status must be in {sorted(ALLOWED_STATUSES)!r}")

    details = {
        "status": payload.get("status"),
        "row_count": len(rows),
        "warn_count": len(warnings),
        "error_count": len(errors),
    }
    return errors, sorted(set(warnings)), details


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(args.scan_json)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "details": {},
            "changed_files": [str(args.output_json)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(
            json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False) + "\n",
            encoding="utf-8",
        )
        print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False))
        return 1

    errors, warnings, details = _validate(payload)
    status = ERROR_STATUS if errors else OK_STATUS

    result = {
        "contract": CONTRACT,
        "status": status,
        "input_json": str(args.scan_json),
        "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
        "errors": errors,
        "warnings": warnings,
        "details": details,
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "changed_files": [str(args.scan_json), str(args.output_json)],
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False))
    return 1 if status != OK_STATUS else 0


if __name__ == "__main__":
    raise SystemExit(main())
