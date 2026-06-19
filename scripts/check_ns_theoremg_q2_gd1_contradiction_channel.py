#!/usr/bin/env python3
"""Validate the fail-closed TheoremG/Q2/GD1 contradiction-channel receipt."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_theoremg_q2_gd1_contradiction_channel.py"
CONTRACT = "check_ns_theoremg_q2_gd1_contradiction_channel"
DEFAULT_RECEIPT = Path(
    "DASHI/Physics/Closure/NSTheoremGQ2GD1ContradictionChannelReceipt.agda"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260619/"
    "ns_theoremg_q2_gd1_contradiction_channel_check_20260620.json"
)

REQUIRED_MODULE_IMPORTS = (
    "DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt",
    "DASHI.Physics.Closure.NSGD1MinPrincipleNoLambda3CollapseReceipt",
    "DASHI.Physics.Closure.NSTheoremGCancellationUpgradeReceipt",
    "DASHI.Physics.Closure.NSLayerL2VorticityFractionReceipt",
    "DASHI.Physics.Closure.NSCollapseConditionalGronwallBridgeReceipt",
)

TRUE_FIELDS = (
    "routeRecorded",
)

FALSE_FIELDS = (
    "q2BlowupLowerImplicationDischarged",
    "q2UniformUpperBoundDischarged",
    "gd1NoCollapseDischarged",
    "theoremGUniformizationDischarged",
    "serrinBKMBridgeDischarged",
    "collapseImpossible",
    "clayNavierStokesPromoted",
)

REQUIRED_TEXT_MARKERS = (
    "finite-time blow-up",
    "Q2/carrier divergence",
    "uniform Q2",
    "BKM/Serrin",
    "fail-closed",
)

CONTROL_CARD = {
    "O": "Owner 5 validates the TheoremG/Q2/GD1 contradiction-channel receipt.",
    "R": (
        "Require the composite route to be recorded while all hard analytic "
        "discharge and promotion gates remain explicitly false."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "A receipt passes only if the five dependency imports are present, the "
        "route-recorded field is true, and every Q2/GD1/TheoremG/BKM/Clay "
        "discharge flag remains false."
    ),
    "L": "Scan the Agda receipt text deterministically and emit a JSON check receipt.",
    "P": "FAIL_CLOSED_THEOREMG_Q2_GD1_CONTRADICTION_CHANNEL",
    "G": "This checker does not infer a theorem or promotion from comments.",
    "F": "Missing imports, missing markers, or promoted gates fail validation.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--receipt",
        type=Path,
        default=DEFAULT_RECEIPT,
        help="Agda receipt to validate.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Path for checker JSON output.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON.")
    return parser.parse_args()


def _field_assignment(text: str, field: str) -> str | None:
    pattern = re.compile(rf";\s*{re.escape(field)}\s*=\s*(true|false)\b")
    match = pattern.search(text)
    return match.group(1) if match else None


def _validate(text: str) -> tuple[list[str], dict[str, Any]]:
    errors: list[str] = []

    import_status = {
        name: name in text
        for name in REQUIRED_MODULE_IMPORTS
    }
    for name, present in import_status.items():
        if not present:
            errors.append(f"missing dependency import marker: {name}")

    true_status = {}
    for field in TRUE_FIELDS:
        value = _field_assignment(text, field)
        true_status[field] = value == "true"
        if value != "true":
            errors.append(f"{field} is not assigned true")

    false_status = {}
    for field in FALSE_FIELDS:
        value = _field_assignment(text, field)
        false_status[field] = value == "false"
        if value != "false":
            errors.append(f"{field} is not assigned false")

    lowered_text = text.lower()
    text_status = {
        marker: marker.lower() in lowered_text
        for marker in REQUIRED_TEXT_MARKERS
    }
    for marker, present in text_status.items():
        if not present:
            errors.append(f"missing route text marker: {marker}")

    details = {
        "dependency_imports": import_status,
        "true_fields": true_status,
        "false_fields": false_status,
        "text_markers": text_status,
    }
    return errors, details


def main() -> int:
    args = _parse_args()
    if not args.receipt.exists():
        raise FileNotFoundError(f"missing receipt: {args.receipt}")

    text = args.receipt.read_text(encoding="utf-8")
    errors, details = _validate(text)
    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "status": "error" if errors else "ok",
        "control_card": CONTROL_CARD,
        "receipt": str(args.receipt),
        "details": details,
        "errors": errors,
        "promotion_gate": False,
        "collapse_impossible": False,
        "clay_navier_stokes_promoted": False,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
