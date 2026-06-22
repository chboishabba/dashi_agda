#!/usr/bin/env python3
"""Derive the positive Wall 1a continuous coherence carrier from floor telemetry.

This scan is intentionally fail-closed. It does not claim an independent theorem
certificate. It normalizes the existing shellwise Wall 1 floor telemetry onto the
continuous carrier identity

    floor = (1 - capacity) / 2

where `capacity` is the signed continuous triadic coherence capacity proxy on
the active shell extraction.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_continuous_coherence_capacity_scan.py"
CONTRACT = "ns_triad_continuous_coherence_capacity_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CONTINUOUS_COHERENCE_CAPACITY_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_COCYCLE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cocycle_floor_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_continuous_coherence_capacity_scan_N128_20260623.json"
)

CONTROL_CARD = {
    "O": "Project the active Wall 1 floor telemetry onto the continuous triadic coherence carrier.",
    "R": (
        "Read shellwise floor telemetry, compute the continuous coherence-capacity proxy and deficit "
        "proxy via the algebraic floor/capacity identity, and emit a fail-closed carrier surface."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "Candidate-only and derived from observed floor telemetry; this is a carrier-identification "
        "surface, not an independent proof certificate."
    ),
    "L": (
        "Flatten the cocycle-floor rows, extract shellwise floor ratios, compute continuous coherence "
        "capacity/deficit proxies, verify the algebraic identity residual, and preserve fail-closed status."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this derived carrier scan.",
    "F": (
        "The scan only records the positive continuous-carrier surface derived from observed floor telemetry; "
        "it does not prove the carrier theorem."
    ),
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
    parser.add_argument("--cocycle-json", type=Path, default=DEFAULT_COCYCLE_JSON)
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


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value)
    return None


def _mean(values: list[float]) -> float:
    return float(sum(values) / len(values)) if values else 0.0


def _cocycle_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    nested = payload.get("triad_cocycle_floor_rows")
    if isinstance(nested, list):
        for frame_row in nested:
            if not isinstance(frame_row, dict):
                continue
            frame = _coerce_int(frame_row.get("frame"))
            shell_rows = frame_row.get("shell_rows")
            if isinstance(shell_rows, list):
                for shell_row in shell_rows:
                    if not isinstance(shell_row, dict):
                        continue
                    row = dict(shell_row)
                    if row.get("frame") is None and frame is not None:
                        row["frame"] = frame
                    if row.get("shell") is None:
                        shell = _coerce_int(row.get("shell_cutoff"))
                        if shell is not None:
                            row["shell"] = shell
                    rows.append(row)
        return rows
    top_rows = payload.get("rows")
    if isinstance(top_rows, list):
        return [row for row in top_rows if isinstance(row, dict)]
    return []


def main() -> int:
    args = _parse_args()
    cocycle_payload = _read_json(args.cocycle_json)
    rows: list[dict[str, Any]] = []
    capacity_values: list[float] = []
    deficit_values: list[float] = []
    floor_values: list[float] = []
    residual_values: list[float] = []

    for source_row in _cocycle_rows(cocycle_payload):
        frame = _coerce_int(source_row.get("frame"))
        shell = _coerce_int(source_row.get("shell"))
        if frame is None or shell is None:
            continue
        floor_ratio = _coerce_float(source_row.get("frustration_floor_ratio_vs_raw"))
        if floor_ratio is None:
            floor_ratio = _coerce_float(source_row.get("floor_ratio_proxy"))
        if floor_ratio is None:
            floor_ratio = 0.0
            status = "partial"
            warnings = ["floor ratio unavailable on source row; defaulted to zero"]
        else:
            status = "ok"
            warnings = []
        floor_ratio = min(max(floor_ratio, 0.0), 0.5)
        capacity = min(max(1.0 - 2.0 * floor_ratio, 0.0), 1.0)
        deficit = min(max(1.0 - capacity, 0.0), 1.0)
        reconstructed_floor = 0.5 * (1.0 - capacity)
        residual = abs(reconstructed_floor - floor_ratio)
        capacity_values.append(capacity)
        deficit_values.append(deficit)
        floor_values.append(floor_ratio)
        residual_values.append(residual)
        rows.append(
            {
                "frame": frame,
                "shell": shell,
                "status": status,
                "candidate_only": True,
                "empirical_non_promoting": True,
                "observed_floor_ratio": floor_ratio,
                "continuous_coherence_capacity_proxy": capacity,
                "continuous_coherence_deficit_proxy": deficit,
                "continuous_floor_reconstructed_from_capacity": reconstructed_floor,
                "continuous_coherence_identity_residual": residual,
                "source_floor_proxy": _coerce_float(source_row.get("frustration_floor_proxy")),
                "source_best_reference_id": source_row.get("best_reference_id"),
                "warnings": warnings,
            }
        )

    aggregate = {
        "shared_frame_shell_count": len(rows),
        "observed_floor_ratio_mean": _mean(floor_values),
        "continuous_coherence_capacity_proxy_mean": _mean(capacity_values),
        "continuous_coherence_deficit_proxy_mean": _mean(deficit_values),
        "continuous_coherence_identity_residual_mean": _mean(residual_values),
        "continuous_coherence_identity_residual_max": max(residual_values) if residual_values else 0.0,
        "continuous_coherence_status": "fail-closed",
        "continuous_coherence_candidate_only": True,
        "continuous_coherence_fail_closed": True,
        "continuous_coherence_theorem_promoted": False,
        "continuous_coherence_full_ns_promoted": False,
        "continuous_coherence_clay_promoted": False,
        "continuous_coherence_route_name": "continuous-coherence-carrier-wall-1a",
        "continuous_coherence_route_story": (
            "Positive Wall 1a carrier surface derived from observed floor telemetry; not an independent certificate."
        ),
        "wall1a_status": "unproved",
    }

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "parameters": {
            "cocycle_json": str(args.cocycle_json),
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
