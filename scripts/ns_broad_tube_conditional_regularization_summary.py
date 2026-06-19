#!/usr/bin/env python3
"""Summarize the broad-tube conditional regularization gate chain.

The script is fail-closed and deterministic. It reads the receipt surfaces for
the four requested gates, requires the expected true/false markers to be
present, records the remaining analytic proof obligations, and keeps Clay
promotion explicitly false.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_broad_tube_conditional_regularization_summary.py"
CONTRACT = "ns_broad_tube_conditional_regularization_summary"
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260619/"
    "ns_broad_tube_conditional_regularization_summary_20260620.json"
)

RECEIPT_SPECS = {
    "nondegenerate_gradient": {
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeNondegenerateGradientReceipt.agda"
        ),
        "true_fields": (
            "smoothLambda2FieldRecorded",
            "gradientLowerBoundOnTubeRecorded",
            "boundedSecondFundamentalFormRecorded",
            "finiteTubularRadiusRecorded",
            "levelSetFoliationRecorded",
        ),
        "false_fields": (
            "unconditionalLambda2GradientTheorem",
            "clayPromotion",
        ),
        "remaining_obligations": (
            "unconditional lambda2-gradient theorem",
            "Clay promotion",
        ),
    },
    "vorticity_coverage": {
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeVorticityCoverageReceipt.agda"
        ),
        "true_fields": (
            "strictCarrierInsufficient",
            "broadTubeRequired",
            "coverageSocketConstructed",
        ),
        "false_fields": (
            "unconditionalCoverageTheorem",
            "clayPromotion",
        ),
        "remaining_obligations": (
            "unconditional coverage theorem",
            "Clay promotion",
        ),
    },
    "serrin_exponent_discharge": {
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeSerrinExponentDischargeReceipt.agda"
        ),
        "true_fields": ("serrinExponentSocketConstructed",),
        "false_fields": (
            "unconditionalSerrinBound",
            "clayPromotion",
        ),
        "remaining_obligations": (
            "unconditional Serrin bound",
            "Clay promotion",
        ),
    },
    "conditional_regularization": {
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeConditionalRegularityTheoremReceipt.agda"
        ),
        "true_fields": (
            "conditionalRegularitySocketConstructed",
        ),
        "false_fields": (
            "unconditionalClayNS",
            "clayPromotion",
        ),
        "remaining_obligations": (
            "unconditional Clay NS theorem",
            "Clay promotion",
        ),
    },
}

CONTROL_CARD = {
    "O": "Owner 5 records the broad-tube conditional regularization summary.",
    "R": (
        "Summarize four conditional broad-tube gates, keep Clay promotion false, and "
        "expose the remaining analytic proof obligations explicitly."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "Fail closed on any missing receipt or missing true/false marker; no promotion "
        "claim is inferred from the receipts."
    ),
    "L": (
        "Read the four receipt surfaces, validate their recorded booleans, derive the "
        "gate flags, and list the residual analytic obligations."
    ),
    "P": "FAIL_CLOSED_NS_BROAD_TUBE_CONDITIONAL_REGULARIZATION_SUMMARY",
    "G": "Clay promotion stays false and every gate remains explicitly conditional.",
    "F": (
        "The ledger is only valid when all four gates are true, Clay promotion is false, "
        "and the expected receipt markers are present."
    ),
}

BOOL_LINE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(true|false)")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Optional output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _read_bool_fields(path: Path) -> dict[str, bool | None]:
    values: dict[str, bool | None] = {}
    for spec in RECEIPT_SPECS.values():
        for name in spec["true_fields"] + spec["false_fields"]:
            values.setdefault(name, None)
    text = path.read_text(encoding="utf-8")
    for match in BOOL_LINE.finditer(text):
        name, raw = match.group(1), match.group(2)
        if name in values:
            values[name] = raw == "true"
    return values


def _evaluate_receipt(
    gate: str, spec: dict[str, Any], errors: list[str]
) -> dict[str, Any]:
    receipt_path = spec["receipt_path"]
    marker_values: dict[str, bool | None] = {name: None for name in spec["true_fields"] + spec["false_fields"]}

    if not receipt_path.exists():
        errors.append(f"missing source receipt: {receipt_path}")
        return {
            "receipt_path": str(receipt_path),
            "gate_flag": False,
            "marker_values": marker_values,
        }

    parsed = _read_bool_fields(receipt_path)
    for name in marker_values:
        marker_values[name] = parsed.get(name)

    true_mode = spec.get("true_mode", "all")
    if true_mode == "any":
        present_true_values = [marker_values.get(name) for name in spec["true_fields"] if marker_values.get(name) is not None]
        if not present_true_values:
            errors.append(
                f"{gate}: missing required true marker one of {', '.join(spec['true_fields'])}"
            )
        elif not any(value is True for value in present_true_values):
            errors.append(
                f"{gate}: expected one of {', '.join(spec['true_fields'])} = true, got {present_true_values!r}"
            )
    else:
        for name in spec["true_fields"]:
            value = marker_values.get(name)
            if value is None:
                errors.append(f"{gate}: missing required true marker {name}")
            elif value is not True:
                errors.append(f"{gate}: expected {name} = true, got {value}")

    for name in spec["false_fields"]:
        value = marker_values.get(name)
        if value is None:
            errors.append(f"{gate}: missing required false marker {name}")
        elif value is not False:
            errors.append(f"{gate}: expected {name} = false, got {value}")

    if true_mode == "any":
        true_ok = any(marker_values.get(name) is True for name in spec["true_fields"])
    else:
        true_ok = all(marker_values.get(name) is True for name in spec["true_fields"])
    gate_flag = true_ok and all(marker_values.get(name) is False for name in spec["false_fields"])

    return {
        "receipt_path": str(receipt_path),
        "gate_flag": gate_flag,
        "marker_values": marker_values,
    }


def _build_output(output_path: Path) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    receipts: dict[str, Any] = {}
    gate_flags: dict[str, bool] = {}
    remaining_obligations: dict[str, list[str]] = {}

    for gate, spec in RECEIPT_SPECS.items():
        result = _evaluate_receipt(gate, spec, errors)
        receipts[gate] = result
        gate_flags[gate] = bool(result["gate_flag"])
        remaining_obligations[gate] = list(spec["remaining_obligations"])

    clay_promotion = False
    if not errors:
        warnings.append("all required receipt markers were parsed and validated.")

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "status": "ok" if not errors else "error",
        "source_receipts": {
            gate: receipts[gate]["receipt_path"] for gate in RECEIPT_SPECS
        },
        "gate_flags": gate_flags,
        "receipt_markers": {gate: receipts[gate]["marker_values"] for gate in RECEIPT_SPECS},
        "promotion_flags": {"clay_promotion": clay_promotion},
        "remaining_analytic_proof_obligations": remaining_obligations,
        "remaining_analytic_proof_obligations_flat": [
            obligation
            for obligations in remaining_obligations.values()
            for obligation in obligations
        ],
        "errors": errors,
        "warnings": warnings,
        "changed_files": [*(str(spec["receipt_path"]) for spec in RECEIPT_SPECS.values()), str(output_path)],
        **CONTROL_CARD,
    }
    return summary


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if pretty:
        text = json.dumps(payload, sort_keys=True, indent=2, allow_nan=False) + "\n"
    else:
        text = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = _parse_args()
    payload = _build_output(args.output)
    _write_json(args.output, payload, args.pretty)
    print(json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if not payload["errors"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
