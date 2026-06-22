#!/usr/bin/env python3
"""Rank current Wall 1 carrier candidates by explanatory support, fail-closed."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_wall1_carrier_explanatory_rank_scan.py"
CONTRACT = "ns_triad_wall1_carrier_explanatory_rank_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_WALL1_CARRIER_EXPLANATORY_RANK_SCAN"
SCHEMA_VERSION = "1.0.0"

DEFAULT_SIGNED_THEOREM_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_wall1_theorem_status_20260622.json"
)
DEFAULT_WALL1_BRIDGE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_wall1_shell_bridge_summary_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_wall1_carrier_explanatory_rank_scan_N128_20260622.json"
)

CONTROL_CARD = {
    "O": "Rank current Wall 1 candidate carriers by explanatory support on the active shell extraction.",
    "R": (
        "Compare cycle-family, raw signed-XOR, signed spectral, and Schur/frame surfaces against the observed "
        "Wall 1 floor and emit a fail-closed carrier-identification ranking."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only ranking telemetry; it narrows the bottleneck but does not prove a carrier theorem.",
    "L": (
        "Read the signed theorem-status and Wall 1 shell-bridge summaries, normalize observed-floor support "
        "against each candidate mechanism, and rank the carriers while preserving fail-closed semantics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this ranking scan.",
    "F": "The scan only ranks current candidates; it does not certify that any surviving carrier is correct.",
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
    parser.add_argument("--signed-theorem-json", type=Path, default=DEFAULT_SIGNED_THEOREM_JSON)
    parser.add_argument("--wall1-bridge-json", type=Path, default=DEFAULT_WALL1_BRIDGE_JSON)
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


def _safe_float(value: Any, default: float = 0.0) -> float:
    if value is None or isinstance(value, bool):
        return default
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return default
    return parsed if parsed == parsed and parsed not in (float("inf"), float("-inf")) else default


def main() -> int:
    args = _parse_args()
    theorem_payload = _read_json(args.signed_theorem_json)
    bridge_payload = _read_json(args.wall1_bridge_json)
    theorem_agg = theorem_payload.get("aggregate", {})
    bridge_agg = bridge_payload.get("aggregate", {})

    observed_floor = _safe_float(theorem_agg.get("observed_floor_ratio_mean"), 0.0)
    eps = max(observed_floor, 1.0e-12)

    carrier_rows = [
        {
            "carrier_id": "cycle-family-local-obstruction",
            "route_name": "cycle-family-lower-bound",
            "support_value": _safe_float(bridge_agg.get("strongest_lower_bound_support_mean"), 0.0),
            "support_ratio_vs_observed_floor": _safe_float(bridge_agg.get("strongest_lower_bound_support_mean"), 0.0) / eps,
            "status": "insufficient",
            "primary_candidate": False,
        },
        {
            "carrier_id": "raw-signed-xor",
            "route_name": "wall1a-signed-xor-gaugeability",
            "support_value": _safe_float(theorem_agg.get("signed_xor_distance_fraction_mean"), 0.0),
            "support_ratio_vs_observed_floor": _safe_float(theorem_agg.get("signed_xor_distance_fraction_mean"), 0.0) / eps,
            "status": "insufficient",
            "primary_candidate": False,
        },
        {
            "carrier_id": "signed-spectral-proxy",
            "route_name": "signed-XY-spectral-frustration-wall-1a",
            "support_value": _safe_float(theorem_agg.get("spectral_floor_lower_bound_mean"), 0.0),
            "support_ratio_vs_observed_floor": _safe_float(theorem_agg.get("spectral_floor_lower_bound_mean"), 0.0) / eps,
            "status": "insufficient",
            "primary_candidate": False,
        },
        {
            "carrier_id": "schur-frame-gap",
            "route_name": "schur-frame-gap-wall-1b",
            "support_value": max(0.0, _safe_float(theorem_agg.get("schur_gap_mean"), 0.0)),
            "support_ratio_vs_observed_floor": max(0.0, _safe_float(theorem_agg.get("schur_gap_mean"), 0.0)) / eps,
            "status": "unproved",
            "primary_candidate": False,
        },
    ]

    carrier_rows.sort(
        key=lambda row: (
            float(row["support_ratio_vs_observed_floor"]),
            float(row["support_value"]),
        ),
        reverse=True,
    )
    for rank, row in enumerate(carrier_rows, start=1):
        row["carrier_rank"] = rank

    top_row = carrier_rows[0] if carrier_rows else None
    aggregate = {
        "observed_floor_ratio_mean": observed_floor,
        "carrier_row_count": len(carrier_rows),
        "carrier_identification_status": "fail-closed",
        "carrier_identification_top_candidate": top_row["carrier_id"] if top_row else None,
        "carrier_identification_top_support_mean": top_row["support_ratio_vs_observed_floor"] if top_row else 0.0,
        "current_primary_carrier_identified": False,
        "signed_discrete_route_explanatory_fraction_mean": _safe_float(theorem_agg.get("signed_xor_distance_fraction_mean"), 0.0) / eps,
        "signed_spectral_route_explanatory_fraction_mean": _safe_float(theorem_agg.get("spectral_floor_lower_bound_mean"), 0.0) / eps,
        "cycle_family_route_explanatory_fraction_mean": _safe_float(bridge_agg.get("strongest_lower_bound_support_mean"), 0.0) / eps,
        "schur_route_explanatory_fraction_mean": max(0.0, _safe_float(theorem_agg.get("schur_gap_mean"), 0.0)) / eps,
        "carrier_story_conclusion": (
            "Observed floor remains real, but current discrete/spectral carriers are not canonical on the active shell extraction."
        ),
    }

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "parameters": {
            "signed_theorem_json": str(args.signed_theorem_json),
            "wall1_bridge_json": str(args.wall1_bridge_json),
            "output_json": str(args.output_json),
        },
        "status": "ok",
        "rows": carrier_rows,
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
