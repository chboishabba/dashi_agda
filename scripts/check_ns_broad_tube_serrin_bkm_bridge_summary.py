#!/usr/bin/env python3
"""Validate the broad-tube Serrin/BKM bridge summary payload."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_broad_tube_serrin_bkm_bridge_summary.py"
CONTRACT = "check_ns_broad_tube_serrin_bkm_bridge_summary"
SOURCE_CONTRACT = "ns_broad_tube_serrin_bkm_bridge_summary"
OK_STATUS = "ok"
ERROR_STATUS = "error"

OPEN_REQUIREMENT_NAMES = (
    "broad_tube_coarea",
    "serrin_lift",
    "bkm_bridge",
)

EXPECTED_REQUIREMENTS = {
    "broad_tube_coarea": [
        "broad_tube_coarea obligation",
        "nondegenerate_lambda2_gradient",
        "finite_tube_thickness",
        "surface_layer_control",
        "coarea_measurability",
    ],
    "serrin_lift": [
        "serrin_lift obligation",
        "finite_tube_coverage",
        "interpolation_exponent_admissibility",
        "velocity_reconstruction",
    ],
    "bkm_bridge": [
        "bkm_bridge obligation",
        "serrin_socket",
        "vorticity_time_integral_control",
        "continuation_criterion",
    ],
}

EXPECTED_REQUIREMENTS_FLAT = [req for reqs in EXPECTED_REQUIREMENTS.values() for req in reqs]

CONTROL_CARD = {
    "O": "Owner 5 validates broad-tube Serrin/BKM bridge summary fields.",
    "R": "Fail-closed validation that gate implementation, promotions, and external obligations are explicit and stable.",
    "C": SCRIPT_NAME,
    "S": (
        "A summary is accepted only if the source ledger explicitly records three conditional gates,"
        " Clay promotion false, and explicit external obligations by gate."
    ),
    "L": (
        "Load summary JSON, validate schema and expected gate/requirement keys,"
        " enforce non-promoting status, and emit a canonical checker receipt."
    ),
    "P": "FAIL_CLOSED_NS_BROAD_TUBE_SERRIN_BKM_BRIDGE_SUMMARY",
    "G": "No route/Clay/theorem promotion is allowed through this checker.",
    "F": "Only a strictly explicit conditional-summary ledger can pass; omitted requirements fail validation.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "summary_json",
        nargs="?",
        type=Path,
        help="Path to ns_broad_tube_serrin_bkm_bridge_summary output JSON.",
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
        default=None,
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


def _validate_requirements(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> None:
    requirements = payload.get("remaining_external_theorem_requirements")
    if not isinstance(requirements, dict):
        _record_error(errors, "missing or invalid remaining_external_theorem_requirements (expected dict)")
        return
    missing = [key for key in OPEN_REQUIREMENT_NAMES if key not in requirements]
    extra = sorted(set(requirements) - set(OPEN_REQUIREMENT_NAMES))
    if missing:
        _record_error(errors, f"missing requirement keys: {', '.join(missing)}")
    if extra:
        _record_error(errors, f"unexpected requirement keys: {', '.join(extra)}")

    for gate, expected in EXPECTED_REQUIREMENTS.items():
        actual_list = requirements.get(gate)
        if not isinstance(actual_list, list):
            _record_error(errors, f"remaining_external_theorem_requirements[{gate}] must be list")
            continue
        if not all(isinstance(item, str) for item in actual_list):
            _record_error(errors, f"remaining_external_theorem_requirements[{gate}] must contain strings")
        if actual_list != list(expected):
            _record_error(
                errors,
                (
                    f"remaining_external_theorem_requirements[{gate}] expected {list(expected)!r}, "
                    f"got {actual_list!r}"
                ),
            )

    actual_flat = payload.get("remaining_external_theorem_requirements_flat")
    if actual_flat is None:
        _record_error(errors, "missing remaining_external_theorem_requirements_flat (expected list)")
    elif actual_flat != EXPECTED_REQUIREMENTS_FLAT:
        _record_error(
            errors,
            (
                f"remaining_external_theorem_requirements_flat expected {EXPECTED_REQUIREMENTS_FLAT!r}, "
                f"got {actual_flat!r}"
            ),
        )


def _validate_promotions(payload: dict[str, Any], errors: list[str]) -> None:
    promotion_flags = payload.get("promotion_flags")
    if not isinstance(promotion_flags, dict):
        _record_error(errors, "missing or invalid promotion_flags dict")
        return
    clay = promotion_flags.get("clay_promotion")
    if clay is not True and clay is not False:
        _record_error(errors, "promotion_flags.clay_promotion must be bool")
    elif clay is not False:
        _record_error(errors, "promotion_flags.clay_promotion must be false")


def _validate_gates(payload: dict[str, Any], errors: list[str]) -> None:
    implemented = payload.get("implemented_conditionally")
    if not isinstance(implemented, dict):
        _record_error(errors, "missing or invalid implemented_conditionally dict")
        return

    missing = [gate for gate in OPEN_REQUIREMENT_NAMES if gate not in implemented]
    extra = sorted(set(implemented) - set(OPEN_REQUIREMENT_NAMES))
    if missing:
        _record_error(errors, f"missing implemented_conditionally gates: {', '.join(missing)}")
    if extra:
        _record_error(errors, f"unexpected implemented_conditionally gates: {', '.join(extra)}")

    for gate in OPEN_REQUIREMENT_NAMES:
        if gate not in implemented:
            continue
        value = implemented.get(gate)
        if isinstance(value, bool):
            if value is not True:
                _record_error(
                    errors,
                    f"implemented_conditionally[{gate}] must be true to represent an explicitly implemented conditional gate",
                )
        else:
            _record_error(errors, f"implemented_conditionally[{gate}] must be bool")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        _record_error(errors, f"contract must be {SOURCE_CONTRACT!r}")

    if payload.get("status") != OK_STATUS:
        _record_error(errors, f"status must be {OK_STATUS!r}")

    _validate_gates(payload, errors)
    _validate_promotions(payload, errors)
    _validate_requirements(payload, errors, warnings)

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
    args: argparse.Namespace
    summary_path: Path

    try:
        args = _parse_args()
        summary_path = _coerce_input_path(args)
    except (ValueError, OSError) as exc:
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
        "implemented_conditionally": payload.get("implemented_conditionally") if payload is not None else None,
        "promotion_flags": payload.get("promotion_flags") if payload is not None else None,
    }

    output_path = args.output_json if args.output_json is not None else None
    if output_path is not None:
        _write_json(output_path, result, pretty=args.pretty)

    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
