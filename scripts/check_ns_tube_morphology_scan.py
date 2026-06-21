#!/usr/bin/env python3
"""Validate the fail-closed tube morphology scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_tube_morphology_scan.py"
CONTRACT = "check_ns_tube_morphology_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TUBE_MORPHOLOGY_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"
ALLOWED_SCAN_STATUSES = {"ok", "partial", "error", "missing_required_field"}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--scan-json",
        type=Path,
        default=Path(
            "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
            "ns_tube_morphology_scan_N128_20260621.json"
        ),
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=Path(
            "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
            "check_ns_tube_morphology_scan_N128_20260621.json"
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
        raise ValueError(f"{path}: payload must be an object")
    return payload


def _ensure_fraction(name: str, value: Any, errors: list[str]) -> None:
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        errors.append(f"{name}: not a float")
        return
    if not math.isfinite(parsed) or parsed < 0.0 or parsed > 1.0:
        errors.append(f"{name}: fraction out of range: {parsed}")


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
        "scan_json": str(args.scan_json),
    }
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _read_json(args.scan_json)
    except Exception as exc:  # noqa: BLE001
        result["status"] = ERROR_STATUS
        result["errors"] = [str(exc)]
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(result, args.pretty))
        return 1

    if payload.get("contract") != "ns_tube_morphology_scan":
        errors.append("unexpected scan contract")
    if payload.get("route_decision") != "FAIL_CLOSED_NS_TUBE_MORPHOLOGY_SCAN":
        errors.append("unexpected scan route_decision")
    if str(payload.get("status")) not in ALLOWED_SCAN_STATUSES:
        errors.append(f"unexpected scan status: {payload.get('status')!r}")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority missing or not object")
    else:
        for key in ("truth_authority", "theorem_authority", "clay_authority", "promoted"):
            if authority.get(key) is not False:
                errors.append(f"authority[{key}] must be false")

    frame_rows = payload.get("frame_rows")
    if not isinstance(frame_rows, list):
        errors.append("frame_rows missing or not list")
        frame_rows = []
    for frame_index, row in enumerate(frame_rows):
        if not isinstance(row, dict):
            errors.append(f"frame_rows[{frame_index}] not object")
            continue
        status = str(row.get("status"))
        if status not in ALLOWED_SCAN_STATUSES:
            errors.append(f"frame_rows[{frame_index}] has bad status {status!r}")
        quantile_rows = row.get("quantile_rows", [])
        if status == OK_STATUS and not isinstance(quantile_rows, list):
            errors.append(f"frame_rows[{frame_index}] quantile_rows missing")
            continue
        if isinstance(quantile_rows, list):
            for quantile_index, qrow in enumerate(quantile_rows):
                if not isinstance(qrow, dict):
                    errors.append(f"frame_rows[{frame_index}].quantile_rows[{quantile_index}] not object")
                    continue
                for name in (
                    "carrier_fraction",
                    "tube_like_fraction",
                    "sheet_like_fraction",
                    "blob_like_fraction",
                    "ambiguous_fraction",
                    "tube_axis_alignment_mean",
                ):
                    _ensure_fraction(
                        f"frame_rows[{frame_index}].quantile_rows[{quantile_index}].{name}",
                        qrow.get(name),
                        errors,
                    )
                total = 0.0
                for name in ("tube_like_fraction", "sheet_like_fraction", "blob_like_fraction", "ambiguous_fraction"):
                    try:
                        total += float(qrow.get(name, 0.0))
                    except (TypeError, ValueError):
                        total = math.nan
                        break
                if math.isfinite(total) and abs(total - 1.0) > 1.0e-6:
                    errors.append(
                        f"frame_rows[{frame_index}].quantile_rows[{quantile_index}] morphology fractions sum to {total}"
                    )

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate missing or not object")
        aggregate = {}
    quantile_rows = aggregate.get("quantile_rows")
    if not isinstance(quantile_rows, list):
        errors.append("aggregate.quantile_rows missing or not list")
        quantile_rows = []
    for quantile_index, qrow in enumerate(quantile_rows):
        if not isinstance(qrow, dict):
            errors.append(f"aggregate.quantile_rows[{quantile_index}] not object")
            continue
        for name in (
            "carrier_fraction_mean",
            "tube_like_fraction",
            "sheet_like_fraction",
            "blob_like_fraction",
            "ambiguous_fraction",
            "tube_axis_alignment_mean",
        ):
            _ensure_fraction(f"aggregate.quantile_rows[{quantile_index}].{name}", qrow.get(name), errors)

    result["status"] = OK_STATUS if not errors else ERROR_STATUS
    result["errors"] = errors
    if warnings:
        result["warnings"] = warnings
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(result, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
