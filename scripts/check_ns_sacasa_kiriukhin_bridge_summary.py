#!/usr/bin/env python3
"""Validate ns_sacasa_kiriukhin_bridge_summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_sacasa_kiriukhin_bridge_summary.py"
CONTRACT = "check_ns_sacasa_kiriukhin_bridge_summary"
SOURCE_CONTRACT = "ns_sacasa_kiriukhin_bridge_summary"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_SACASA_KIRIUKHIN_BRIDGE_SUMMARY"
CHECK_ROUTE_DECISION = "FAIL_CLOSED_NS_SACASA_KIRIUKHIN_BRIDGE_SUMMARY_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, ERROR_STATUS}
EXPECTED_SOURCE_NAMES = ("orbit_phase_scan", "non_sobolev_scan")
EXPECTED_SOURCE_STATUSES = {OK_STATUS, ERROR_STATUS}

DEFAULT_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_sacasa_kiriukhin_bridge_summary_20260621.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_sacasa_kiriukhin_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate the orbit-phase/non-Sobolev bridge summary schema and source routes.",
    "R": (
        "Verify the explicit source-route ledger, shared-key bridge surface, compact correlations, "
        "and the unproved live-wall marker."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed validation: missing routes, malformed source payloads, or authority drift are hard errors.",
    "L": "Load the bridge summary JSON, validate schema, source routes, aggregate surface, and emit a checker receipt.",
    "P": CHECK_ROUTE_DECISION,
    "G": "No theorem, Clay, or proof claim is permitted through this checker.",
    "F": "The live wall must remain explicitly unproved and the summary must remain empirically scoped.",
}

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "summary_json",
        nargs="?",
        type=Path,
        help="Path to ns_sacasa_kiriukhin_bridge_summary output JSON.",
    )
    parser.add_argument(
        "--summary-json",
        type=Path,
        dest="summary_json_kw",
        help="Alternative named input path.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Optional checker receipt output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print checker receipt.")
    return parser.parse_args()


def _coerce_input_path(args: argparse.Namespace) -> Path:
    if args.summary_json is not None and args.summary_json_kw is not None:
        raise ValueError("provide either positional summary-json path or --summary-json, not both")
    if args.summary_json is None and args.summary_json_kw is None:
        return DEFAULT_SUMMARY
    return args.summary_json if args.summary_json is not None else args.summary_json_kw


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing summary json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"summary payload must be an object: {path}")
    return payload


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = (
        json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
        if pretty
        else json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)
    ) + "\n"
    path.write_text(text, encoding="utf-8")


def _record_error(errors: list[str], path: str, message: str) -> None:
    errors.append(f"{path}: {message}")


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    value = value.strip()
    return value if value else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _coerce_finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        parsed = int(value)
        return parsed if parsed >= 0 else None
    return None


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        if _coerce_nonempty_str(payload.get(key)) is None:
            _record_error(errors, "control_card", f"{key} must be a non-empty string")


def _check_contract(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("contract") != SOURCE_CONTRACT:
        _record_error(errors, "contract", f"must be {SOURCE_CONTRACT!r}")


def _check_route(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        _record_error(errors, "route_decision", f"must be {SOURCE_ROUTE_DECISION!r}")


def _check_status(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("status") not in ALLOWED_STATUSES:
        _record_error(errors, "status", f"must be one of {sorted(ALLOWED_STATUSES)!r}")


def _check_schema_version(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("schema_version") != SCHEMA_VERSION:
        _record_error(errors, "schema_version", f"must be {SCHEMA_VERSION!r}")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        _record_error(errors, "authority", "must be a dict")
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
    for key, expected_value in expected.items():
        value = _coerce_bool(authority.get(key))
        if value is None:
            _record_error(errors, f"authority.{key}", "must be bool")
            continue
        if value is not expected_value:
            _record_error(errors, f"authority.{key}", f"must be {expected_value!r}")


def _check_inputs(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> None:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, "inputs", "must be a dict")
        return
    for key in ("orbit_phase_json", "non_sobolev_json", "output_json"):
        if _coerce_nonempty_str(inputs.get(key)) is None:
            warnings.append(f"inputs.{key} should be a non-empty string")


def _check_source_routes(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> None:
    routes = payload.get("source_routes")
    if not isinstance(routes, dict):
        _record_error(errors, "source_routes", "must be a dict")
        return

    missing = [name for name in EXPECTED_SOURCE_NAMES if name not in routes]
    extra = sorted(set(routes) - set(EXPECTED_SOURCE_NAMES))
    if missing:
        _record_error(errors, "source_routes", f"missing routes: {', '.join(missing)}")
    if extra:
        _record_error(errors, "source_routes", f"unexpected routes: {', '.join(extra)}")

    for name in EXPECTED_SOURCE_NAMES:
        route = routes.get(name)
        if not isinstance(route, dict):
            _record_error(errors, f"source_routes.{name}", "must be a dict")
            continue
        present = _coerce_bool(route.get("present"))
        if present is not True:
            _record_error(errors, f"source_routes.{name}.present", "must be true")
        status = route.get("status")
        if status not in EXPECTED_SOURCE_STATUSES:
            _record_error(errors, f"source_routes.{name}.status", f"must be one of {sorted(EXPECTED_SOURCE_STATUSES)!r}")
        if _coerce_nonempty_str(route.get("path")) is None:
            warnings.append(f"source_routes.{name}.path should be a non-empty string")
        if _coerce_nonnegative_int(route.get("row_count")) is None:
            _record_error(errors, f"source_routes.{name}.row_count", "must be nonnegative int")
        if _coerce_nonnegative_int(route.get("usable_row_count")) is None:
            _record_error(errors, f"source_routes.{name}.usable_row_count", "must be nonnegative int")


def _check_bridge_rows(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> list[float]:
    rows = payload.get("bridge_rows")
    if not isinstance(rows, list):
        _record_error(errors, "bridge_rows", "must be a list")
        return []

    phases: list[float] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, f"bridge_rows[{index}]", "must be a dict")
            continue
        phase = _coerce_finite_float(row.get("orbit_phase"))
        if phase is None:
            _record_error(errors, f"bridge_rows[{index}].orbit_phase", "must be finite float")
            continue
        phases.append(round(phase, 12))

        for name in ("orbit_coherence", "orbit_extra", "non_sobolev_metric"):
            value = row.get(name)
            if value is not None and _coerce_finite_float(value) is None:
                _record_error(errors, f"bridge_rows[{index}].{name}", "must be finite float or null")

        live_wall = _coerce_bool(row.get("live_wall_unproved"))
        if live_wall is not False:
            _record_error(errors, f"bridge_rows[{index}].live_wall_unproved", "must be false")

        label = row.get("phase_label")
        if label is not None and _coerce_nonempty_str(label) is None:
            warnings.append(f"bridge_rows[{index}].phase_label should be a non-empty string or null")

    if len(phases) != len(set(phases)):
        _record_error(errors, "bridge_rows", "duplicate orbit_phase values")
    return phases


def _check_bridge_surface(payload: dict[str, Any], row_phases: list[float], errors: list[str], warnings: list[str]) -> None:
    surface = payload.get("bridge_surface")
    if not isinstance(surface, dict):
        _record_error(errors, "bridge_surface", "must be a dict")
        return

    for key in (
        "orbit_phase_row_count",
        "non_sobolev_row_count",
        "shared_key_count",
        "orbit_only_key_count",
        "non_sobolev_only_key_count",
        "bridge_row_count",
    ):
        if _coerce_nonnegative_int(surface.get(key)) is None:
            _record_error(errors, f"bridge_surface.{key}", "must be nonnegative int")

    coverage = _coerce_finite_float(surface.get("coverage_fraction"))
    if coverage is None:
        _record_error(errors, "bridge_surface.coverage_fraction", "must be finite float")
    elif coverage < 0.0 or coverage > 1.0:
        _record_error(errors, "bridge_surface.coverage_fraction", "must lie in [0, 1]")

    correlations = surface.get("correlations")
    if not isinstance(correlations, dict):
        _record_error(errors, "bridge_surface.correlations", "must be a dict")
    else:
        for key in (
            "orbit_phase_vs_coherence",
            "orbit_phase_vs_non_sobolev",
            "coherence_vs_non_sobolev",
        ):
            value = correlations.get(key)
            if value is not None:
                corr = _coerce_finite_float(value)
                if corr is None or corr < -1.0 or corr > 1.0:
                    _record_error(errors, f"bridge_surface.correlations.{key}", "must be finite float in [-1, 1] or null")

    coherence = surface.get("coherence")
    if not isinstance(coherence, dict):
        _record_error(errors, "bridge_surface.coherence", "must be a dict")
    else:
        for key in ("orbit", "non_sobolev", "orbit_extra"):
            stats = coherence.get(key)
            if not isinstance(stats, dict):
                _record_error(errors, f"bridge_surface.coherence.{key}", "must be a dict")
                continue
            if _coerce_nonnegative_int(stats.get("count")) is None:
                _record_error(errors, f"bridge_surface.coherence.{key}.count", "must be nonnegative int")
            for stat_key in ("min", "max", "mean"):
                value = stats.get(stat_key)
                if value is not None and _coerce_finite_float(value) is None:
                    warnings.append(f"bridge_surface.coherence.{key}.{stat_key} should be finite float or null")

    if surface.get("live_wall_proved") is not False:
        _record_error(errors, "bridge_surface.live_wall_proved", "must be false")
    if surface.get("live_wall_status") != "unproved":
        _record_error(errors, "bridge_surface.live_wall_status", "must be 'unproved'")

    if _coerce_nonnegative_int(surface.get("bridge_row_count")) is not None and surface.get("bridge_row_count") != len(set(row_phases)):
        warnings.append(
            f"bridge_surface.bridge_row_count={surface.get('bridge_row_count')} differs from bridge row count={len(set(row_phases))}"
        )


def _check_live_wall(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("live_wall_proved") is not False:
        _record_error(errors, "live_wall_proved", "must be false")
    if payload.get("live_wall_status") != "unproved":
        _record_error(errors, "live_wall_status", "must be 'unproved'")


def _check_summary(payload: dict[str, Any]) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    if _coerce_nonempty_str(payload.get("contract")) is None:
        _record_error(errors, "contract", "missing contract")
    if _coerce_nonempty_str(payload.get("schema_version")) is None:
        _record_error(errors, "schema_version", "missing schema_version")

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, errors)
    _check_status(payload, errors)
    _check_schema_version(payload, errors)
    _check_authority(payload, errors)
    _check_inputs(payload, errors, warnings)
    _check_source_routes(payload, errors, warnings)
    row_phases = _check_bridge_rows(payload, errors, warnings)
    _check_bridge_surface(payload, row_phases, errors, warnings)
    _check_live_wall(payload, errors)

    return sorted(set(errors)), sorted(set(warnings))


def main() -> int:
    try:
        args = _parse_args()
        summary_path = _coerce_input_path(args)
    except (OSError, ValueError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"summary_json": None, "output_json": None},
            "changed_files": [],
            **CONTROL_CARD,
        }
        print(json.dumps(result, sort_keys=True, indent=2))
        return 1

    inputs = {
        "summary_json": str(summary_path),
        "output_json": str(args.output_json),
    }
    changed_files = [str(summary_path), str(args.output_json)]

    try:
        payload = _load_json(summary_path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors = [str(exc)]
        warnings: list[str] = []
        status = ERROR_STATUS
    else:
        errors, warnings = _check_summary(payload)
        status = OK_STATUS if not errors else ERROR_STATUS

    result = {
        "contract": CONTRACT,
        "status": status,
        "errors": errors,
        "warnings": warnings,
        "inputs": inputs,
        "checked_contract": SOURCE_CONTRACT,
        "checked_summary_path": str(summary_path),
        "changed_files": changed_files,
        "summary_preview": {
            "status": payload.get("status") if "payload" in locals() and isinstance(payload, dict) else None,
            "contract": payload.get("contract") if "payload" in locals() and isinstance(payload, dict) else None,
            "route_decision": payload.get("route_decision") if "payload" in locals() and isinstance(payload, dict) else None,
            "live_wall_status": payload.get("live_wall_status") if "payload" in locals() and isinstance(payload, dict) else None,
        },
        **CONTROL_CARD,
    }

    _write_json(args.output_json, result, args.pretty)
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
