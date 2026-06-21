#!/usr/bin/env python3
"""Validate the tube/pressure/helicity bridge summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_tube_pressure_helicity_bridge_summary.py"
CONTRACT = "check_ns_tube_pressure_helicity_bridge_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TUBE_PRESSURE_HELICITY_BRIDGE_SUMMARY_CHECK"
SCHEMA_VERSION = "1.0.0"
OK_STATUS = "ok"
ERROR_STATUS = "error"
ALLOWED_SUMMARY_STATUSES = {"ok", "partial", "error"}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--summary-json",
        type=Path,
        default=Path(
            "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
            "ns_tube_pressure_helicity_bridge_summary_20260621.json"
        ),
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=Path(
            "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
            "check_ns_tube_pressure_helicity_bridge_summary_20260621.json"
        ),
    )
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


def _ensure_fraction(name: str, value: Any, errors: list[str]) -> None:
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        errors.append(f"{name}: not a float")
        return
    if not math.isfinite(parsed) or parsed < 0.0 or parsed > 1.0:
        errors.append(f"{name}: out of range {parsed}")


def main() -> int:
    args = _parse_args()
    result: dict[str, Any] = {
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
        "summary_json": str(args.summary_json),
    }
    errors: list[str] = []
    try:
        payload = _read_json(args.summary_json)
    except Exception as exc:  # noqa: BLE001
        result["status"] = ERROR_STATUS
        result["errors"] = [str(exc)]
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(result, args.pretty))
        return 1

    if payload.get("contract") != "ns_tube_pressure_helicity_bridge_summary":
        errors.append("unexpected summary contract")
    if payload.get("route_decision") != "FAIL_CLOSED_NS_TUBE_PRESSURE_HELICITY_BRIDGE_SUMMARY":
        errors.append("unexpected route_decision")
    if str(payload.get("status")) not in ALLOWED_SUMMARY_STATUSES:
        errors.append(f"unexpected summary status: {payload.get('status')!r}")

    sources = payload.get("sources")
    if not isinstance(sources, dict):
        errors.append("sources missing or not object")
    else:
        for name in ("morphology", "boundary_helicity", "boundary_pressure"):
            source = sources.get(name)
            if not isinstance(source, dict):
                errors.append(f"sources.{name} missing")

    bridge_rows = payload.get("bridge_rows")
    if not isinstance(bridge_rows, list):
        errors.append("bridge_rows missing or not list")
        bridge_rows = []
    for row_index, row in enumerate(bridge_rows):
        if not isinstance(row, dict):
            errors.append(f"bridge_rows[{row_index}] not object")
            continue
        for name in (
            "tube_like_fraction",
            "sheet_like_fraction",
            "blob_like_fraction",
            "tube_axis_alignment_mean",
            "q_negative_fraction",
            "p11_negative_fraction",
            "depleting_pair_fraction",
            "helicity_positive_fraction",
        ):
            _ensure_fraction(f"bridge_rows[{row_index}].{name}", row.get(name), errors)
        q_corr = row.get("q_helicity_correlation")
        if q_corr is not None:
            try:
                parsed = float(q_corr)
            except (TypeError, ValueError):
                errors.append(f"bridge_rows[{row_index}].q_helicity_correlation not float")
            else:
                if not math.isfinite(parsed) or parsed < -1.0 or parsed > 1.0:
                    errors.append(f"bridge_rows[{row_index}].q_helicity_correlation out of range {parsed}")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate missing or not object")
    else:
        for key, value in aggregate.items():
            if key == "shared_frame_count":
                continue
            if value is None:
                continue
            try:
                parsed = float(value)
            except (TypeError, ValueError):
                errors.append(f"aggregate.{key} not float")
                continue
            if not math.isfinite(parsed) or parsed < -1.0 or parsed > 1.0:
                errors.append(f"aggregate.{key} correlation out of range {parsed}")

    result["status"] = OK_STATUS if not errors else ERROR_STATUS
    result["errors"] = errors
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(result, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
