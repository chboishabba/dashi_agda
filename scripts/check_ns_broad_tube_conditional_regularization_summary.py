#!/usr/bin/env python3
"""Validate the broad-tube conditional regularization summary payload."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_broad_tube_conditional_regularization_summary.py"
CONTRACT = "check_ns_broad_tube_conditional_regularization_summary"
SOURCE_CONTRACT = "ns_broad_tube_conditional_regularization_summary"
OK_STATUS = "ok"
ERROR_STATUS = "error"
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260619/"
    "ns_broad_tube_conditional_regularization_summary_regression_20260620.json"
)

EXPECTED_GATES = (
    "nondegenerate_gradient",
    "vorticity_coverage",
    "serrin_exponent_discharge",
    "conditional_regularization",
)

CONTROL_CARD = {
    "O": "Owner 5 validates the broad-tube conditional regularization summary fields.",
    "R": "Fail-closed validation that gate status, promotion suppression, and obligation reporting are explicit.",
    "C": SCRIPT_NAME,
    "S": (
        "A summary is accepted only if it records four true gates, Clay promotion false, "
        "and a stable residual-obligation surface."
    ),
    "L": (
        "Load the summary JSON, validate the gate set and promotion flags, and emit a "
        "canonical checker receipt."
    ),
    "P": "FAIL_CLOSED_NS_BROAD_TUBE_CONDITIONAL_REGULARIZATION_SUMMARY",
    "G": "No route, theorem, or Clay promotion is inferred by this checker.",
    "F": "Only an explicit conditional-summary ledger can pass; missing gates fail validation.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "summary_json",
        nargs="?",
        type=Path,
        help="Path to ns_broad_tube_conditional_regularization_summary output JSON.",
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
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output JSON.")
    return parser.parse_args()


def _coerce_input_path(args: argparse.Namespace) -> Path:
    if args.summary_json is not None and args.summary_json_kw is not None:
        raise ValueError("provide either positional summary-json path or --summary-json, not both")
    if args.summary_json is None and args.summary_json_kw is None:
        raise ValueError("provide a summary JSON input path")
    return args.summary_json if args.summary_json is not None else args.summary_json_kw


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input summary: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level payload is not an object: {path}")
    return payload


def _record_error(errors: list[str], message: str) -> None:
    errors.append(message)


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        _record_error(errors, f"contract must be {SOURCE_CONTRACT!r}")

    if payload.get("status") != OK_STATUS:
        _record_error(errors, f"status must be {OK_STATUS!r}")

    gate_flags = payload.get("gate_flags")
    if not isinstance(gate_flags, dict):
        _record_error(errors, "missing or invalid gate_flags dict")
    else:
        missing = [gate for gate in EXPECTED_GATES if gate not in gate_flags]
        extra = sorted(set(gate_flags) - set(EXPECTED_GATES))
        if missing:
            _record_error(errors, f"missing gate flags: {', '.join(missing)}")
        if extra:
            _record_error(errors, f"unexpected gate flags: {', '.join(extra)}")
        for gate in EXPECTED_GATES:
            if gate not in gate_flags:
                continue
            value = gate_flags.get(gate)
            if value is not True:
                _record_error(errors, f"gate_flags[{gate}] must be true")

    promotion_flags = payload.get("promotion_flags")
    if not isinstance(promotion_flags, dict):
        _record_error(errors, "missing or invalid promotion_flags dict")
    else:
        clay = promotion_flags.get("clay_promotion")
        if clay is not False:
            _record_error(errors, "promotion_flags.clay_promotion must be false")

    obligations = payload.get("remaining_analytic_proof_obligations")
    if not isinstance(obligations, dict):
        _record_error(errors, "missing or invalid remaining_analytic_proof_obligations dict")
    if not isinstance(payload.get("remaining_analytic_proof_obligations_flat"), list):
        _record_error(errors, "missing remaining_analytic_proof_obligations_flat list")

    if not isinstance(payload.get("changed_files"), list):
        warnings.append("changed_files should be a list of touched artifact paths")

    return sorted(set(errors)), sorted(set(warnings))


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    text = (
        json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
        if pretty
        else json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)
    ) + "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = _parse_args()
    try:
        summary_path = _coerce_input_path(args)
    except (ValueError, OSError) as exc:
        output_json = str(getattr(args, "output_json", None)) if getattr(args, "output_json", None) is not None else None
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"summary_json": None, "output_json": output_json},
            "changed_files": [output_json] if output_json is not None else [],
            **CONTROL_CARD,
        }
        if output_json is not None:
            _write_json(args.output_json, result, pretty=args.pretty)
        print(json.dumps(result, sort_keys=True, indent=2))
        return 1

    inputs = {
        "summary_json": str(summary_path),
        "output_json": str(args.output_json) if args.output_json is not None else None,
    }
    changed_files = [str(summary_path)]
    if args.output_json is not None:
        changed_files.append(str(args.output_json))

    payload: dict[str, Any] | None = None
    try:
        payload = _load_json(summary_path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors = [str(exc)]
        warnings: list[str] = []
        status = ERROR_STATUS
    else:
        errors, warnings = _validate(payload)
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
        **CONTROL_CARD,
    }

    result["summary_payload_preview"] = {
        "status": payload.get("status") if payload is not None else None,
        "contract": payload.get("contract") if payload is not None else None,
        "gate_flags": payload.get("gate_flags") if payload is not None else None,
        "promotion_flags": payload.get("promotion_flags") if payload is not None else None,
    }

    output_path = args.output_json if args.output_json is not None else None
    if output_path is not None:
        _write_json(output_path, result, pretty=args.pretty)

    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
