#!/usr/bin/env python3
"""Reconcile signed Wall 1 carrier surfaces against the active fail-closed extraction."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_signed_carrier_reconciliation_scan.py"
CONTRACT = "ns_triad_signed_carrier_reconciliation_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_CARRIER_RECONCILIATION_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_GAUGEABILITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_xor_gaugeability_scan_N128_20260622.json"
)
DEFAULT_SPECTRAL_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_spectral_audit_scan_N128_20260622.json"
)
DEFAULT_THEOREM_STATUS_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_wall1_theorem_status_20260622.json"
)
DEFAULT_THEOREM_STATUS_CSV = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "wall1_theorem_status.csv"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_carrier_reconciliation_scan_N128_20260622.json"
)

CONTROL_CARD = {
    "O": "Reconcile signed Wall 1 chart/status surfaces against the active fail-closed extraction.",
    "R": (
        "Compare the repo-local theorem-status CSV and JSON against the signed gaugeability and signed spectral "
        "extractions, expose any row/coverage mismatch, and make the canonical fail-closed interpretation explicit."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only reconciliation telemetry; it governs interpretation but does not prove Wall 1.",
    "L": (
        "Load the signed theorem-status CSV and JSON plus the signed gaugeability and spectral scans, "
        "normalize on shared frame-shell keys, compare core fields, and emit fail-closed reconciliation rows."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this reconciliation scan.",
    "F": "The scan only reconciles surfaces; it does not identify the correct Wall 1a carrier by itself.",
}

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gaugeability-json", type=Path, default=DEFAULT_GAUGEABILITY_JSON)
    parser.add_argument("--spectral-json", type=Path, default=DEFAULT_SPECTRAL_JSON)
    parser.add_argument("--theorem-status-json", type=Path, default=DEFAULT_THEOREM_STATUS_JSON)
    parser.add_argument("--theorem-status-csv", type=Path, default=DEFAULT_THEOREM_STATUS_CSV)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: payload must be object")
    return payload


def _safe_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    value = payload.get("rows")
    if isinstance(value, list):
        return [row for row in value if isinstance(row, dict)]
    return []


def _key(row: dict[str, Any]) -> tuple[int, int] | None:
    frame = row.get("frame")
    shell = row.get("shell", row.get("shell_n"))
    if not isinstance(frame, int) or not isinstance(shell, int):
        return None
    return frame, shell


def _read_csv_rows(path: Path) -> list[dict[str, Any]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        return [dict(row) for row in reader]


def _float_match(left: Any, right: Any, tol: float = 1.0e-9) -> bool:
    lval = _safe_float(left)
    rval = _safe_float(right)
    if lval is None or rval is None:
        return False
    scale = max(1.0, abs(lval), abs(rval))
    return abs(lval - rval) <= tol * scale


def _mean(values: list[float]) -> float:
    return float(sum(values) / len(values)) if values else 0.0


def main() -> int:
    args = _parse_args()
    gauge_payload = _read_json(args.gaugeability_json)
    spectral_payload = _read_json(args.spectral_json)
    theorem_status_payload = _read_json(args.theorem_status_json)
    theorem_status_csv_rows = _read_csv_rows(args.theorem_status_csv)

    gauge_by_key = {_key(row): row for row in _rows(gauge_payload) if _key(row) is not None}
    spectral_by_key = {_key(row): row for row in _rows(spectral_payload) if _key(row) is not None}
    theorem_status_by_key = {_key(row): row for row in _rows(theorem_status_payload) if _key(row) is not None}

    csv_by_key: dict[tuple[int, int], dict[str, Any]] = {}
    for row in theorem_status_csv_rows:
        frame = row.get("frame")
        shell = row.get("shell")
        if frame is None or shell is None:
            continue
        try:
            key = (int(frame), int(shell))
        except ValueError:
            continue
        csv_by_key[key] = row

    shared_keys = sorted(set(csv_by_key) & set(theorem_status_by_key) & set(gauge_by_key) & set(spectral_by_key))
    rows: list[dict[str, Any]] = []
    csv_theorem_matches: list[float] = []
    csv_gauge_matches: list[float] = []
    csv_spectral_matches: list[float] = []

    for frame, shell in shared_keys:
        csv_row = csv_by_key[(frame, shell)]
        theorem_row = theorem_status_by_key[(frame, shell)]
        gauge_row = gauge_by_key[(frame, shell)]
        spectral_row = spectral_by_key[(frame, shell)]

        csv_theorem_core = all(
            (
                _float_match(csv_row.get("observed_floor_ratio"), theorem_row.get("observed_floor_ratio")),
                _float_match(csv_row.get("signed_xor_distance_fraction"), theorem_row.get("signed_xor_distance_fraction")),
                _float_match(csv_row.get("spectral_floor_lower_bound"), theorem_row.get("spectral_floor_lower_bound")),
                _float_match(csv_row.get("identity_error_op"), theorem_row.get("identity_error_op")),
            )
        )
        csv_gauge_core = all(
            (
                _float_match(csv_row.get("psi_pi_fraction"), gauge_row.get("psi_pi_weight_fraction")),
                _float_match(csv_row.get("signed_xor_distance_fraction"), gauge_row.get("signed_xor_weighted_distance_fraction")),
            )
        )
        csv_spectral_core = all(
            (
                _float_match(csv_row.get("spectral_floor_lower_bound"), spectral_row.get("xy_floor_spectral_lower_bound")),
                _float_match(csv_row.get("signed_laplacian_lambda_min"), spectral_row.get("signed_laplacian_lambda_min")),
                _float_match(csv_row.get("signed_laplacian_lambda_max"), spectral_row.get("signed_laplacian_lambda_max")),
                _float_match(csv_row.get("identity_error_op"), spectral_row.get("identity_error_op")),
            )
        )
        csv_theorem_matches.append(1.0 if csv_theorem_core else 0.0)
        csv_gauge_matches.append(1.0 if csv_gauge_core else 0.0)
        csv_spectral_matches.append(1.0 if csv_spectral_core else 0.0)

        rows.append(
            {
                "frame": frame,
                "shell": shell,
                "status": "ok",
                "csv_matches_theorem_status_core": csv_theorem_core,
                "csv_matches_gaugeability_core": csv_gauge_core,
                "csv_matches_spectral_core": csv_spectral_core,
                "observed_floor_ratio": float(theorem_row.get("observed_floor_ratio", 0.0)),
                "signed_xor_distance_fraction": float(theorem_row.get("signed_xor_distance_fraction", 0.0)),
                "spectral_floor_lower_bound": float(theorem_row.get("spectral_floor_lower_bound", 0.0)),
                "identity_error_op": float(theorem_row.get("identity_error_op", 0.0)),
                "legacy_signed_story_noncanonical": bool(
                    (_safe_float(theorem_row.get("observed_floor_ratio")) or 0.0) > 0.0
                    and (_safe_float(theorem_row.get("signed_xor_distance_fraction")) or 0.0) <= 1.0e-12
                    and (_safe_float(theorem_row.get("spectral_floor_lower_bound")) or 0.0) <= 1.0e-12
                ),
                "reconciliation_required": True,
            }
        )

    theorem_row_count = len(theorem_status_by_key)
    csv_row_count = len(csv_by_key)
    gauge_row_count = len(gauge_by_key)
    spectral_row_count = len(spectral_by_key)
    coverage_den = max(gauge_row_count, spectral_row_count, 1)
    shared_count = len(shared_keys)
    aggregate = {
        "shared_frame_shell_count": shared_count,
        "theorem_status_row_count": theorem_row_count,
        "csv_row_count": csv_row_count,
        "gaugeability_row_count": gauge_row_count,
        "spectral_row_count": spectral_row_count,
        "csv_vs_theorem_status_core_match_fraction": _mean(csv_theorem_matches),
        "csv_vs_gaugeability_core_match_fraction": _mean(csv_gauge_matches),
        "csv_vs_spectral_core_match_fraction": _mean(csv_spectral_matches),
        "coverage_fraction_vs_signed_extractions": float(shared_count / coverage_den),
        "observed_floor_ratio_mean": _mean(
            [float(row["observed_floor_ratio"]) for row in rows]
        ),
        "signed_xor_distance_fraction_mean": _mean(
            [float(row["signed_xor_distance_fraction"]) for row in rows]
        ),
        "spectral_floor_lower_bound_mean": _mean(
            [float(row["spectral_floor_lower_bound"]) for row in rows]
        ),
        "identity_error_op_mean": _mean(
            [float(row["identity_error_op"]) for row in rows]
        ),
        "legacy_signed_story_noncanonical_fraction": _mean(
            [1.0 if row["legacy_signed_story_noncanonical"] else 0.0 for row in rows]
        ),
        "signed_carrier_reconciliation_status": "fail-closed",
        "optimistic_chart_noncanonical": True,
        "reconciliation_required": True,
        "canonical_signed_route": "fail-closed-extraction",
    }

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "parameters": {
            "gaugeability_json": str(args.gaugeability_json),
            "spectral_json": str(args.spectral_json),
            "theorem_status_json": str(args.theorem_status_json),
            "theorem_status_csv": str(args.theorem_status_csv),
            "output_json": str(args.output_json),
        },
        "status": "ok",
        "rows": rows,
        "aggregate": aggregate,
        "warnings": [],
        "errors": [],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
