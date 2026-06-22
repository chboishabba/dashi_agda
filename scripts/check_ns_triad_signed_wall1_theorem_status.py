#!/usr/bin/env python3
"""Validate signed Wall 1 theorem-status summary output."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_signed_wall1_theorem_status.py"
CONTRACT = "check_ns_triad_signed_wall1_theorem_status"
SOURCE_CONTRACT = "ns_triad_signed_wall1_theorem_status"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_signed_wall1_theorem_status.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_WALL1_THEOREM_STATUS"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_WALL1_THEOREM_STATUS_CHECK"
SCHEMA_VERSION = "1.0.0"

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_wall1_theorem_status_20260622.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_signed_wall1_theorem_status_20260622.json"
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


def main() -> int:
    args = _parse_args()
    payload = _load_json(_input_path(args))
    errors: list[str] = []
    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if aggregate.get("wall1a_status") != "unproved":
            errors.append("aggregate.wall1a_status: must be 'unproved'")
        if aggregate.get("wall1b_status") != "unproved":
            errors.append("aggregate.wall1b_status: must be 'unproved'")
        signed_status = aggregate.get("signed_wall1_status")
        if signed_status not in ("fail-closed", "unavailable"):
            errors.append("aggregate.signed_wall1_status: must be 'fail-closed' or 'unavailable'")
        signed_consensus = aggregate.get("signed_surface_consensus")
        if signed_consensus not in ("fail-closed", "unavailable"):
            errors.append("aggregate.signed_surface_consensus: must be 'fail-closed' or 'unavailable'")
        if signed_status == "fail-closed" and aggregate.get("signed_wall1_row_count") != 2:
            errors.append("aggregate.signed_wall1_row_count: must be 2 when signed wall1 is fail-closed")
        if signed_status == "fail-closed" and aggregate.get("signed_wall1_surface_count") != 2:
            errors.append("aggregate.signed_wall1_surface_count: must be 2 when signed wall1 is fail-closed")
        if signed_status == "unavailable" and payload.get("signed_wall1_rows"):
            errors.append("aggregate.signed_wall1_status: unavailable requires no signed_wall1_rows")
        if signed_consensus == "unavailable" and payload.get("signed_wall1_rows"):
            errors.append("aggregate.signed_surface_consensus: unavailable requires no signed_wall1_rows")
        if aggregate.get("signed_wall1_candidate_only") is not True:
            errors.append("aggregate.signed_wall1_candidate_only: must be true")
        if aggregate.get("signed_wall1_fail_closed") is not True:
            errors.append("aggregate.signed_wall1_fail_closed: must be true")
        if aggregate.get("signed_wall1_theorem_promoted") is not False:
            errors.append("aggregate.signed_wall1_theorem_promoted: must be false")
        if aggregate.get("signed_wall1_full_ns_promoted") is not False:
            errors.append("aggregate.signed_wall1_full_ns_promoted: must be false")
        if aggregate.get("signed_wall1_clay_promoted") is not False:
            errors.append("aggregate.signed_wall1_clay_promoted: must be false")
        if aggregate.get("signed_xor_bridge_open") is not True:
            errors.append("aggregate.signed_xor_bridge_open: must be true")
        if aggregate.get("signed_spectral_bridge_open") is not True:
            errors.append("aggregate.signed_spectral_bridge_open: must be true")
        if aggregate.get("signed_wall1_route_names") is not None and not isinstance(
            aggregate.get("signed_wall1_route_names"), list
        ):
            errors.append("aggregate.signed_wall1_route_names: must be list or null")
        if aggregate.get("signed_wall1_route_names") not in (
            None,
            ["wall1a-signed-xor-gaugeability", "signed-XY-spectral-frustration-wall-1a"],
        ):
            errors.append(
                "aggregate.signed_wall1_route_names: must be the ordered signed Wall 1 route list"
            )

    signed_wall1_rows = payload.get("signed_wall1_rows")
    if not isinstance(signed_wall1_rows, list):
        errors.append("signed_wall1_rows: must be list")
        signed_wall1_rows = []
    if len(signed_wall1_rows) != 2:
        errors.append("signed_wall1_rows: must contain exactly 2 rows")
    for index, row in enumerate(signed_wall1_rows):
        if not isinstance(row, dict):
            errors.append(f"signed_wall1_rows[{index}]: must be object")
            continue
        if row.get("surface") not in ("signed_xor_gaugeability", "signed_spectral_frustration"):
            errors.append(
                f"signed_wall1_rows[{index}].surface: must be 'signed_xor_gaugeability' or 'signed_spectral_frustration'"
            )
        if not isinstance(row.get("module_path"), str):
            errors.append(f"signed_wall1_rows[{index}].module_path: must be string")
        if not isinstance(row.get("receipt_name"), str):
            errors.append(f"signed_wall1_rows[{index}].receipt_name: must be string")
        if not isinstance(row.get("route_name"), str):
            errors.append(f"signed_wall1_rows[{index}].route_name: must be string")
        if not isinstance(row.get("boundary_summary"), str):
            errors.append(f"signed_wall1_rows[{index}].boundary_summary: must be string")
        if not isinstance(row.get("bridge_summary"), str):
            errors.append(f"signed_wall1_rows[{index}].bridge_summary: must be string")
        if row.get("candidate_only") is not True:
            errors.append(f"signed_wall1_rows[{index}].candidate_only: must be true")
        if row.get("fail_closed") is not True:
            errors.append(f"signed_wall1_rows[{index}].fail_closed: must be true")
        if row.get("theorem_promoted") is not False:
            errors.append(f"signed_wall1_rows[{index}].theorem_promoted: must be false")
        if row.get("full_ns_promoted") is not False:
            errors.append(f"signed_wall1_rows[{index}].full_ns_promoted: must be false")
        if row.get("clay_promoted") is not False:
            errors.append(f"signed_wall1_rows[{index}].clay_promoted: must be false")
        if row.get("wall1_status") != "unproved":
            errors.append(f"signed_wall1_rows[{index}].wall1_status: must be 'unproved'")
        if row.get("surface") == "signed_xor_gaugeability":
            if row.get("route_name") != "wall1a-signed-xor-gaugeability":
                errors.append(
                    f"signed_wall1_rows[{index}].route_name: must be 'wall1a-signed-xor-gaugeability'"
                )
            if row.get("boundary_summary") != (
                "Sign balance does not imply frustration; gaugeable signed XOR is satisfiable; the non-gaugeable signed XOR obstruction surface remains empirical."
            ):
                errors.append(
                    f"signed_wall1_rows[{index}].boundary_summary: must match the canonical signed XOR note"
                )
            if row.get("bridge_summary") != (
                "The weighted-distance bridge to gaugeability remains open; d_W(b, im B₂) is the quantitative target."
            ):
                errors.append(
                    f"signed_wall1_rows[{index}].bridge_summary: must match the canonical signed XOR bridge note"
                )
            if row.get("weighted_distance_target_text") != "d_W(b, im B₂)":
                errors.append(
                    f"signed_wall1_rows[{index}].weighted_distance_target_text: must be 'd_W(b, im B₂)'"
                )
            if row.get("gaugeable_signed_xor_satisfiable") is not True:
                errors.append(f"signed_wall1_rows[{index}].gaugeable_signed_xor_satisfiable: must be true")
            if row.get("non_gaugeable_signed_xor_is_actual_obstruction_surface") is not True:
                errors.append(
                    f"signed_wall1_rows[{index}].non_gaugeable_signed_xor_is_actual_obstruction_surface: must be true"
                )
            if row.get("signed_xor_bridge_open") is not True:
                errors.append(f"signed_wall1_rows[{index}].signed_xor_bridge_open: must be true")
        else:
            if row.get("route_name") != "signed-XY-spectral-frustration-wall-1a":
                errors.append(
                    f"signed_wall1_rows[{index}].route_name: must be 'signed-XY-spectral-frustration-wall-1a'"
                )
            if row.get("boundary_summary") != (
                "Signed Laplacian / signed XY floor candidate remains open, upper spectral edge still carries XY-floor risk, and theorem/full-NS/Clay promotion stays false."
            ):
                errors.append(
                    f"signed_wall1_rows[{index}].boundary_summary: must match the canonical signed spectral note"
                )
            if row.get("bridge_summary") != (
                "The discrete signed-XOR distance to the continuous XY floor bridge is still open."
            ):
                errors.append(
                    f"signed_wall1_rows[{index}].bridge_summary: must match the canonical signed spectral bridge note"
                )
            if row.get("primary_wall1a_candidate") is not True:
                errors.append(f"signed_wall1_rows[{index}].primary_wall1a_candidate: must be true")
            if row.get("upper_spectral_edge_carries_xy_floor_risk") is not True:
                errors.append(f"signed_wall1_rows[{index}].upper_spectral_edge_carries_xy_floor_risk: must be true")
            if row.get("signed_xor_distance_bridge_open") is not True:
                errors.append(f"signed_wall1_rows[{index}].signed_xor_distance_bridge_open: must be true")
    out = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "source_contract": SOURCE_CONTRACT,
        "source_script_name": SOURCE_SCRIPT_NAME,
        "ok": not errors,
        "status": "ok" if not errors else "error",
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(out, pretty=args.pretty), encoding="utf-8")
    print(_json_text(out, pretty=args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
