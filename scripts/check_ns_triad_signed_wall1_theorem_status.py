#!/usr/bin/env python3
"""Validate signed Wall 1 theorem-status summary output."""

from __future__ import annotations

import argparse
import json
import math
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

ALLOWED_SIGNED_STATUS = {"fail-closed", "partial", "unavailable"}
ALLOWED_SIGNED_SOURCE = {
    "reconciliation_json",
    "carrier_ranking_json",
    "carrier_ranking_json+continuous_coherence_capacity_json",
    "k_n_exact_identity_json",
    "legacy_chart",
    "missing",
    "explicit",
    "legacy-optimistic-chart",
    "source-json",
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
        for key in ("signed_carrier_reconciliation_status", "carrier_identification_status"):
            if aggregate.get(key) not in ALLOWED_SIGNED_STATUS:
                errors.append(f"aggregate.{key}: must be one of {sorted(ALLOWED_SIGNED_STATUS)!r}")
        for key in ("signed_carrier_reconciliation_source", "carrier_identification_source"):
            if aggregate.get(key) not in ALLOWED_SIGNED_SOURCE:
                errors.append(f"aggregate.{key}: must be one of {sorted(ALLOWED_SIGNED_SOURCE)!r}")
        if aggregate.get("signed_carrier_reconciliation_status") == "fail-closed" and aggregate.get("signed_carrier_reconciliation_source") == "missing":
            errors.append("aggregate.signed_carrier_reconciliation_source: fail-closed status requires a non-missing provenance tag")
        if aggregate.get("carrier_identification_status") == "fail-closed" and aggregate.get("carrier_identification_source") == "missing":
            errors.append("aggregate.carrier_identification_source: fail-closed status requires a non-missing provenance tag")
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
        if aggregate.get("k_n_exact_identity_status") not in ("fail-closed", "partial", "unavailable"):
            errors.append(
                "aggregate.k_n_exact_identity_status: must be 'fail-closed', 'partial', or 'unavailable'"
            )
        if aggregate.get("continuous_coherence_capacity_status") not in ("fail-closed", "partial", "unavailable"):
            errors.append(
                "aggregate.continuous_coherence_capacity_status: must be 'fail-closed', 'partial', or 'unavailable'"
            )
        if aggregate.get("k_n_exact_identity_candidate_only") is not True:
            errors.append("aggregate.k_n_exact_identity_candidate_only: must be true")
        if aggregate.get("k_n_exact_identity_fail_closed") is not True:
            errors.append("aggregate.k_n_exact_identity_fail_closed: must be true")
        if aggregate.get("continuous_coherence_capacity_source") not in (
            "continuous_coherence_capacity_json",
            "missing",
            "explicit",
            "source-json",
        ):
            errors.append(
                "aggregate.continuous_coherence_capacity_source: must be 'continuous_coherence_capacity_json', 'missing', 'explicit', or 'source-json'"
            )
        for key in (
            "continuous_coherence_capacity_proxy_mean",
            "continuous_coherence_deficit_proxy_mean",
            "continuous_coherence_route_explanatory_fraction_mean",
        ):
            value = _finite_float(aggregate.get(key))
            if value is None or value < -1.0e-12:
                errors.append(f"aggregate.{key}: must be finite nonnegative")
        for key in ("continuous_coherence_identity_residual_mean", "continuous_coherence_identity_residual_max"):
            value = _finite_float(aggregate.get(key))
            if value is None or value < -1.0e-12:
                errors.append(f"aggregate.{key}: must be finite nonnegative")
        if aggregate.get("k_n_exact_identity_status") not in ("fail-closed", "unavailable"):
            errors.append("aggregate.k_n_exact_identity_status: must be 'fail-closed' or 'unavailable'")
        if aggregate.get("k_n_exact_identity_route_names") not in (
            None,
            ["k-n-exact-identity-wall-1a", "b-s-frame-equidistribution-wall-1a"],
        ):
            errors.append(
                "aggregate.k_n_exact_identity_route_names: must be the ordered K_N exact-identity route list"
            )
        if aggregate.get("continuous_wall1_status") not in ("fail-closed", "unavailable"):
            errors.append("aggregate.continuous_wall1_status: must be 'fail-closed' or 'unavailable'")
        if aggregate.get("continuous_wall1_candidate_only") is not True:
            errors.append("aggregate.continuous_wall1_candidate_only: must be true")
        if aggregate.get("continuous_wall1_fail_closed") is not True:
            errors.append("aggregate.continuous_wall1_fail_closed: must be true")
        if aggregate.get("continuous_wall1_theorem_promoted") is not False:
            errors.append("aggregate.continuous_wall1_theorem_promoted: must be false")
        if aggregate.get("continuous_wall1_full_ns_promoted") is not False:
            errors.append("aggregate.continuous_wall1_full_ns_promoted: must be false")
        if aggregate.get("continuous_wall1_clay_promoted") is not False:
            errors.append("aggregate.continuous_wall1_clay_promoted: must be false")
        if aggregate.get("continuous_wall1_route_names") not in (
            None,
            ["k-n-exact-identity-wall-1a", "b-s-frame-equidistribution-wall-1a"],
        ):
            errors.append(
                "aggregate.continuous_wall1_route_names: must be the ordered continuous Wall 1 route list"
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
        if row.get("signed_carrier_reconciliation_status") is not None and row.get("signed_carrier_reconciliation_status") not in ALLOWED_SIGNED_STATUS:
            errors.append(
                f"signed_wall1_rows[{index}].signed_carrier_reconciliation_status: must be fail-closed|partial|unavailable or null"
            )
        if row.get("carrier_identification_status") is not None and row.get("carrier_identification_status") not in ALLOWED_SIGNED_STATUS:
            errors.append(
                f"signed_wall1_rows[{index}].carrier_identification_status: must be fail-closed|partial|unavailable or null"
            )
        if row.get("signed_carrier_reconciliation_source") is not None and row.get("signed_carrier_reconciliation_source") not in ALLOWED_SIGNED_SOURCE:
            errors.append(
                f"signed_wall1_rows[{index}].signed_carrier_reconciliation_source: must be an allowed provenance tag or null"
            )
        if row.get("carrier_identification_source") is not None and row.get("carrier_identification_source") not in ALLOWED_SIGNED_SOURCE:
            errors.append(
                f"signed_wall1_rows[{index}].carrier_identification_source: must be an allowed provenance tag or null"
            )
        if row.get("carrier_rank") is not None and _finite_float(row.get("carrier_rank")) is None:
            errors.append(f"signed_wall1_rows[{index}].carrier_rank: must be finite or null")
        if row.get("carrier_id") is not None and not isinstance(row.get("carrier_id"), str):
            errors.append(f"signed_wall1_rows[{index}].carrier_id: must be string or null")
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
                "Signed Laplacian / signed XY floor candidate remains open, upper spectral edge still carries XY-floor risk, theorem/full-NS/Clay promotion stays false, and the old signed route is legacy and non-canonical."
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
    continuous_wall1_rows = payload.get("continuous_wall1_rows")
    if not isinstance(continuous_wall1_rows, list):
        errors.append("continuous_wall1_rows: must be list")
        continuous_wall1_rows = []
    if len(continuous_wall1_rows) != 2:
        errors.append("continuous_wall1_rows: must contain exactly 2 rows")
    for index, row in enumerate(continuous_wall1_rows):
        if not isinstance(row, dict):
            errors.append(f"continuous_wall1_rows[{index}]: must be object")
            continue
        if row.get("surface") not in ("k_n_exact_identity_carrier", "b_s_frame_equidistribution_boundary"):
            errors.append(
                f"continuous_wall1_rows[{index}].surface: must be 'k_n_exact_identity_carrier' or 'b_s_frame_equidistribution_boundary'"
            )
        for key in ("module_path", "receipt_name", "route_name", "boundary_summary", "bridge_summary"):
            if not isinstance(row.get(key), str):
                errors.append(f"continuous_wall1_rows[{index}].{key}: must be string")
        if row.get("route_name") != "k-n-exact-identity-wall-1a" and row.get("surface") == "k_n_exact_identity_carrier":
            errors.append(
                f"continuous_wall1_rows[{index}].route_name: must be 'k-n-exact-identity-wall-1a'"
            )
        if row.get("surface") == "k_n_exact_identity_carrier" and row.get("boundary_summary") != (
            "The K_N exact-identity candidate is the positive Wall 1a carrier, while the old signed-XOR route is legacy and non-canonical."
        ):
            errors.append(
                f"continuous_wall1_rows[{index}].boundary_summary: must match the canonical K_N exact-identity note"
            )
        if row.get("surface") == "k_n_exact_identity_carrier" and row.get("bridge_summary") != (
            "This exact-identity surface is candidate-only and fail-closed; it keeps the positive theorem target explicit without claiming an independent certificate."
        ):
            errors.append(
                f"continuous_wall1_rows[{index}].bridge_summary: must match the canonical K_N exact-identity note"
            )
        if row.get("surface") == "b_s_frame_equidistribution_boundary":
            if row.get("route_name") != "b-s-frame-equidistribution-wall-1a":
                errors.append(
                    f"continuous_wall1_rows[{index}].route_name: must be 'b-s-frame-equidistribution-wall-1a'"
                )
            if row.get("boundary_summary") != (
                "The Biot-Savart frame-equidistribution target is the single open finite-dimensional theorem candidate; lower spectral edge controls the floor and upper edge controls frame safety."
            ):
                errors.append(
                    f"continuous_wall1_rows[{index}].boundary_summary: must match the canonical frame-equidistribution note"
                )
            if row.get("bridge_summary") != (
                "This equidistribution surface is candidate-only and fail-closed; it keeps the exact operator theorem target explicit without claiming a proof."
            ):
                errors.append(
                    f"continuous_wall1_rows[{index}].bridge_summary: must match the canonical frame-equidistribution note"
                )
        if row.get("candidate_only") is not True:
            errors.append(f"continuous_wall1_rows[{index}].candidate_only: must be true")
        if row.get("fail_closed") is not True:
            errors.append(f"continuous_wall1_rows[{index}].fail_closed: must be true")
        if row.get("theorem_promoted") is not False:
            errors.append(f"continuous_wall1_rows[{index}].theorem_promoted: must be false")
        if row.get("full_ns_promoted") is not False:
            errors.append(f"continuous_wall1_rows[{index}].full_ns_promoted: must be false")
        if row.get("clay_promoted") is not False:
            errors.append(f"continuous_wall1_rows[{index}].clay_promoted: must be false")
        if row.get("wall1_status") != "unproved":
            errors.append(f"continuous_wall1_rows[{index}].wall1_status: must be 'unproved'")
        if row.get("k_n_exact_identity_route_open") is not True:
            errors.append(f"continuous_wall1_rows[{index}].k_n_exact_identity_route_open: must be true")
        if row.get("k_n_exact_identity_status") not in ("fail-closed", "partial", "unavailable"):
            errors.append(
                f"continuous_wall1_rows[{index}].k_n_exact_identity_status: must be 'fail-closed', 'partial', or 'unavailable'"
            )
        if row.get("continuous_coherence_route_open") is not True:
            errors.append(f"continuous_wall1_rows[{index}].continuous_coherence_route_open: must be true")
        if row.get("continuous_coherence_status") not in ("fail-closed", "partial", "unavailable"):
            errors.append(
                f"continuous_wall1_rows[{index}].continuous_coherence_status: must be 'fail-closed', 'partial', or 'unavailable'"
            )
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
