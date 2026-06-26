#!/usr/bin/env python3
"""Validate ns_triad_frustration_bridge_summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_frustration_bridge_summary.py"
CONTRACT = "check_ns_triad_frustration_bridge_summary"
SOURCE_CONTRACT = "ns_triad_frustration_bridge_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRUSTRATION_BRIDGE_SUMMARY_CHECK"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRUSTRATION_BRIDGE_SUMMARY"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frustration_bridge_summary_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_frustration_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate the triad-frustration bridge summary output.",
    "R": "Check schema, authority flags, bridge rows, and the explicit unproved-wall marker.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed triad-frustration bridge summaries.",
    "L": "Load the summary JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field or authority drift is a hard error.",
}

SOURCE_CONTROL_CARD = {
    "O": "Summarize the triad cocycle/frustration/adversarial telemetry surfaces.",
    "R": (
        "Join the shared frame keys across the three new scans, then emit compact "
        "bridge rows, correlations, and explicit unproved-wall markers."
    ),
    "C": "scripts/ns_triad_frustration_bridge_summary.py",
    "S": "Fail-closed on missing inputs, malformed rows, or absent shared keys; telemetry only.",
    "L": (
        "Normalize each scan onto a shared frame key, compute bridge rows and "
        "simple correlations, and expose the live wall as unproved."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this summary.",
    "F": "The finite-dimensional carrier is measured only; the Sacasa bridge remains unproved.",
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


def main() -> int:
    args = _parse_args()
    path = _input_path(args)
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        receipt = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(receipt, args.pretty))
        return 1

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("status") not in {OK_STATUS, ERROR_STATUS}:
        errors.append("status: must be ok|error")
    if not isinstance(payload.get("ok"), bool):
        errors.append("ok: must be bool")
    if payload.get("script") != SOURCE_CONTROL_CARD["C"]:
        errors.append(f"script: must be {SOURCE_CONTROL_CARD['C']!r}")
    if payload.get("control_card") != SOURCE_CONTROL_CARD:
        errors.append("control_card: must match canonical summary control card")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        expected = {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        }
        for key, value in expected.items():
            if authority.get(key) is not value:
                errors.append(f"authority.{key}: must be {value!r}")

    rows = payload.get("bridge_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("bridge_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"bridge_rows[{index}]: must be object")
            continue
        if _nonnegative_int(row.get("frame")) is None:
            errors.append(f"bridge_rows[{index}].frame: must be nonnegative int")
        if row.get("live_wall_unproved") is not False:
            errors.append(f"bridge_rows[{index}].live_wall_unproved: must be false")
        triad_count = row.get("triad_count")
        if triad_count is not None and _nonnegative_int(triad_count) is None:
            errors.append(f"bridge_rows[{index}].triad_count: must be nonnegative int or null")
        mode_count = row.get("mode_count")
        if mode_count is not None and _nonnegative_int(mode_count) is None:
            errors.append(f"bridge_rows[{index}].mode_count: must be nonnegative int or null")
        for key in (
            "incidence_density",
            "cycle_rank_proxy",
            "exact_lock_proxy",
            "frustration_residual",
            "coherence_loss_proxy",
            "triad_weight_concentration",
            "adversarial_gain",
            "best_phase",
            "baseline_score",
            "best_score",
        ):
            value = row.get(key)
            if value is not None and _finite_float(value) is None:
                errors.append(f"bridge_rows[{index}].{key}: must be finite or null")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    if _nonnegative_int(aggregate.get("shared_frame_count")) is None:
        errors.append("aggregate.shared_frame_count: must be nonnegative int")
    coverage = _finite_float(aggregate.get("coverage_fraction"))
    if coverage is None or coverage < 0.0 or coverage > 1.0 + 1.0e-12:
        errors.append("aggregate.coverage_fraction: must lie in [0,1]")
    for key in (
        "cycle_rank_proxy_mean",
        "frustration_residual_mean",
        "adversarial_gain_mean",
        "exact_lock_proxy_mean",
        "coherence_loss_proxy_mean",
        "cycle_rank_vs_frustration_correlation",
        "frustration_vs_adversarial_gain_correlation",
        "exact_lock_vs_coherence_loss_correlation",
    ):
        value = aggregate.get(key)
        if value is not None:
            parsed = _finite_float(value)
            if parsed is None:
                errors.append(f"aggregate.{key}: must be finite or null")
            elif "correlation" in key and (parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12):
                errors.append(f"aggregate.{key}: correlation must lie in [-1,1]")
    if aggregate.get("live_wall_status") != "unproved":
        errors.append("aggregate.live_wall_status: must be 'unproved'")
    if aggregate.get("live_wall_proved") is not False:
        errors.append("aggregate.live_wall_proved: must be false")

    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "warnings": warnings,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
