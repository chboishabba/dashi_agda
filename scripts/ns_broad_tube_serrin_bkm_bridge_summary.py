#!/usr/bin/env python3
"""Summarize broad-tube Serrin → BKM conditional bridge status for receipts.

The script emits a deterministic, non-promoting summary ledger that records:
- three gates marked as implemented conditionally (coarea, Serrin lift, BKM),
- explicit `clay_promotion = false`, and
- explicit remaining external-theorem requirements per gate.

This is intentionally fail-closed on malformed input and supports deterministic CI
re-use via sorted JSON output.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_broad_tube_serrin_bkm_bridge_summary.py"
CONTRACT = "ns_broad_tube_serrin_bkm_bridge_summary"
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260619/ns_broad_tube_serrin_bkm_bridge_summary_20260620.json"
)
DEFAULT_RECEIPT = Path("DASHI/Physics/Closure/NSBroadTubeSerrinLiftGapReceipt.agda")

OPEN_REQUIREMENT_NAMES = (
    "broad_tube_coarea",
    "serrin_lift",
    "bkm_bridge",
)

GATE_EXPECTED_TRUE = {
    "broad_tube_coarea": True,
    "serrin_lift": True,
    "bkm_bridge": True,
}

GATE_REQUIREMENTS = {
    "broad_tube_coarea": (
        "broad_tube_coarea obligation",
        "nondegenerate_lambda2_gradient",
        "finite_tube_thickness",
        "surface_layer_control",
        "coarea_measurability",
    ),
    "serrin_lift": (
        "serrin_lift obligation",
        "finite_tube_coverage",
        "interpolation_exponent_admissibility",
        "velocity_reconstruction",
    ),
    "bkm_bridge": (
        "bkm_bridge obligation",
        "serrin_socket",
        "vorticity_time_integral_control",
        "continuation_criterion",
    ),
}

CONTROL_CARD = {
    "O": "Owner 5 records broad-tube Serrin/BKM bridge summary status.",
    "R": (
        "Summarize conditional gate implementation, explicit promotion suppression, "
        "and remaining external theorem requirements from the broad-tube Serrin-BKM chain."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "Fail-closed summary-only ledger; only existing receipt fields are synthesized and no"
        " theorem promotion is inferred."
    ),
    "L": (
        "Read the gap-receipt booleans, map them into the three canonical gates,"
        " and enumerate remaining external obligations by gate."
    ),
    "P": "FAIL_CLOSED_NS_BROAD_TUBE_SERRIN_BKM_BRIDGE_SUMMARY",
    "G": "Clay promotion and full BKM unconditional closure stay explicitly false/open.",
    "F": (
        "The three gates remain conditional with explicit obligations; no theorem claims or"
        " Clay promotion are recorded."
    ),
}

REQUIRED_AGDA_FIELDS = (
    "calc8WeightedLambda2EvidenceFlag",
    "strictCarrierSufficient",
    "broadTubeRequired",
    "broadTubeInteriorContinuationOpenFlag",
    "serrinLiftRequired",
    "bkmBridgeRequired",
    "clayPromotion",
)

_BOOL_LINE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(true|false)")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--receipt-path",
        type=Path,
        default=DEFAULT_RECEIPT,
        help="Optional path to NSBroadTubeSerrinLiftGapReceipt.agda.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Optional output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _read_bool_fields(path: Path) -> dict[str, bool | None]:
    values: dict[str, bool | None] = {name: None for name in REQUIRED_AGDA_FIELDS}
    text = path.read_text(encoding="utf-8")
    for match in _BOOL_LINE.finditer(text):
        name, raw = match.group(1), match.group(2)
        if name in values:
            values[name] = True if raw == "true" else False
    return values


def _build_output(payload_path: Path, booleans: dict[str, bool | None]) -> tuple[dict[str, Any], list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    for name in REQUIRED_AGDA_FIELDS:
        if booleans.get(name) is None:
            errors.append(f"Missing boolean field in Agda receipt: {name}")

    implemented_conditionally: dict[str, bool] = {}
    for gate in OPEN_REQUIREMENT_NAMES:
        if gate == "broad_tube_coarea":
            receipt_field = "broadTubeInteriorContinuationOpenFlag"
        elif gate == "serrin_lift":
            receipt_field = "serrinLiftRequired"
        else:
            receipt_field = "bkmBridgeRequired"

        flag = booleans.get(receipt_field)
        if flag is None:
            implemented = False
        else:
            implemented = bool(flag)

        implemented_conditionally[gate] = implemented
        if implemented != GATE_EXPECTED_TRUE[gate]:
            errors.append(
                f"{gate}: expected {GATE_EXPECTED_TRUE[gate]} for {receipt_field}, got {implemented}"
            )

    remaining_requirements = {
        gate: list(requirements)
        for gate, requirements in GATE_REQUIREMENTS.items()
    }

    flattened = [
        req
        for gate_reqs in GATE_REQUIREMENTS.values()
        for req in gate_reqs
    ]

    status = "ok" if not errors else "error"
    if status == "ok":
        warnings.extend(["Agda receipt fields were parsed and validated."])

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "source_receipt": str(payload_path),
        "strict_carrier_sufficient": booleans.get("strictCarrierSufficient"),
        "broad_tube_required": booleans.get("broadTubeRequired"),
        "implemented_conditionally": implemented_conditionally,
        "promotion_flags": {
            "clay_promotion": booleans.get("clayPromotion"),
        },
        "remaining_external_theorem_requirements": remaining_requirements,
        "remaining_external_theorem_requirements_flat": flattened,
        "errors": errors,
        "warnings": warnings,
        "changed_files": [str(payload_path)],
        **CONTROL_CARD,
    }

    return summary, errors, warnings


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if pretty:
        text = json.dumps(payload, sort_keys=True, indent=2, allow_nan=False) + "\n"
    else:
        text = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = _parse_args()

    if not args.receipt_path.exists():
        payload = {
            "contract": CONTRACT,
            "status": "error",
            "errors": [f"missing source receipt: {args.receipt_path}"],
            "warnings": [],
            "changed_files": [str(args.receipt_path), str(args.output)],
            **CONTROL_CARD,
            "implemented_conditionally": {gate: False for gate in OPEN_REQUIREMENT_NAMES},
            "promotion_flags": {"clay_promotion": None},
            "remaining_external_theorem_requirements": {gate: list(reqs) for gate, reqs in GATE_REQUIREMENTS.items()},
            "remaining_external_theorem_requirements_flat": [
                req
                for reqs in GATE_REQUIREMENTS.values()
                for req in reqs
            ],
            "source_receipt": str(args.receipt_path),
        }
        _write_json(args.output, payload, args.pretty)
        print(json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None))
        return 1

    booleans = _read_bool_fields(args.receipt_path)
    payload, errors, _warnings = _build_output(args.receipt_path, booleans)
    payload["changed_files"] = [str(args.receipt_path), str(args.output)]

    _write_json(args.output, payload, args.pretty)
    print(json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
