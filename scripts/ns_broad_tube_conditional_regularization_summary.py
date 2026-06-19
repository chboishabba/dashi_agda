#!/usr/bin/env python3
"""Summarize the broad-tube conditional regularization gate chain.

The script is fail-closed and deterministic. It reads the receipt surfaces for
the four requested gates, requires the expected true/false and proof-kernel
markers to be present, records the remaining analytic proof obligations, and
keeps Clay promotion explicitly false.
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
        "record_name": "NSBroadTubeNondegenerateGradientReceipt",
        "canonical_name": "canonicalNSBroadTubeNondegenerateGradientReceipt",
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeNondegenerateGradientReceipt.agda"
        ),
        "true_fields": (
            "smoothLambda2FieldRecorded",
            "gradientLowerBoundOnTubeRecorded",
            "boundedSecondFundamentalFormRecorded",
            "finiteTubularRadiusRecorded",
            "levelSetFoliationRecorded",
            "allAnalyticAssumptionsStillPresent",
        ),
        "false_fields": (
            "unconditionalLambda2GradientTheorem",
            "clayPromotion",
        ),
        "analytic_markers": {
            "nondegenerate_exact_surface": {
                "rellich_formula_recorded": {
                    "kind": "list_member",
                    "list_name": "canonicalNSBroadTubeNondegenerateGradientExactAssumptions",
                    "member": "rellichFirstDerivativeFormula",
                },
                "kato_formula_recorded": {
                    "kind": "list_member",
                    "list_name": "canonicalNSBroadTubeNondegenerateGradientExactAssumptions",
                    "member": "katoHessianLaplacianFormula",
                },
                "coarea_nondegeneracy_ae_recorded": {
                    "kind": "list_member",
                    "list_name": "canonicalNSBroadTubeNondegenerateGradientExactAssumptions",
                    "member": "coareaNondegeneracyAERecorded",
                },
                "pointwise_blocker_required": {
                    "kind": "list_member",
                    "list_name": "canonicalNSBroadTubeNondegenerateGradientExactAssumptions",
                    "member": "pointwiseLowerBoundNeedsNonFlatNoCriticalManifold",
                },
                "coarea_ae_bool_recorded": {
                    "kind": "bool_field",
                    "field": "coareaAEMeasureTheoreticRecorded",
                },
            }
        },
        "remaining_obligations": (
            "unconditional lambda2-gradient theorem",
            "Clay promotion",
        ),
    },
    "vorticity_coverage": {
        "record_name": "NSBroadTubeVorticityCoverageReceipt",
        "canonical_name": "canonicalNSBroadTubeVorticityCoverageReceipt",
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeVorticityCoverageReceipt.agda"
        ),
        "true_fields": (
            "strictCarrierInsufficient",
            "broadTubeRequired",
            "broadLayerFractionTelemetryRecorded",
            "coverageSocketConstructed",
        ),
        "false_fields": (
            "unconditionalCoverageTheorem",
            "assumptionsDischarged",
            "clayPromotion",
        ),
        "analytic_markers": {
            "vorticity_surface_split_interior_exterior": {
                "coarea_split_recorded": {
                    "kind": "bool_field",
                    "field": "broadTubeLambda2SplitRecorded",
                },
                "deep_interior_gronwall_recorded": {
                    "kind": "bool_field",
                    "field": "deepInteriorGronwallRecorded",
                },
                "exterior_pressure_cz_l3_recorded": {
                    "kind": "bool_field",
                    "field": "exteriorPressureCZL3Recorded",
                },
                "l3_conditionality_recorded": {
                    "kind": "bool_field",
                    "field": "l3EnstrophyConditionalityRecorded",
                },
                "ce0t_constant_route_recorded": {
                    "kind": "string_contains",
                    "name": "conditionalL2GlobalBoundFormula",
                    "needle": "C(E0, T)",
                },
            }
        },
        "remaining_obligations": (
            "unconditional coverage theorem",
            "Clay promotion",
        ),
    },
    "serrin_exponent_discharge": {
        "record_name": "NSBroadTubeSerrinExponentDischargeReceipt",
        "canonical_name": "canonicalNSBroadTubeSerrinExponentDischargeReceipt",
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeSerrinExponentDischargeReceipt.agda"
        ),
        "true_fields": ("serrinExponentSocketConstructed",),
        "false_fields": (
            "unconditionalSerrinBound",
            "clayPromotion",
        ),
        "analytic_markers": {
            "serrin_exact_surface": {
                "serrin_pair_8_4_recorded": {
                    "kind": "nat_pair",
                    "p_name": "serrinAdmissibleP",
                    "q_name": "serrinAdmissibleQ",
                    "p_value": 8,
                    "q_value": 4,
                },
                "serrin_critical_relation_marker_recorded": {
                    "kind": "string_contains",
                    "name": "serrinCriticalRelationMarker",
                    "needle": "2/8 + 3/4 = 1",
                },
                "circularity_blocker_recorded": {
                    "kind": "list_member",
                    "list_name": "canonicalNSBroadTubeSerrinExponentAnalyticRoutes",
                    "member": "circularSobolevCalderonChainRejected",
                },
                "theoremg_q2_requirement_recorded": {
                    "kind": "list_members",
                    "list_name": "canonicalNSBroadTubeSerrinExponentRequiredInputs",
                    "members": ("q2RequiredInput", "theoremGRequiredInput"),
                },
                "q2_gd1_contradiction_route_recorded": {
                    "kind": "list_members",
                    "list_name": "canonicalNSBroadTubeSerrinExponentRequiredInputs",
                    "members": ("q2RequiredInput", "gd1RequiredInput"),
                },
                "velocity_l8l4_insufficient_recorded": {
                    "kind": "list_member",
                    "list_name": "canonicalNSBroadTubeSerrinExponentAnalyticRoutes",
                    "member": "l84NotEnoughForBkmL1Linf",
                },
            }
        },
        "remaining_obligations": (
            "unconditional Serrin bound",
            "Clay promotion",
        ),
    },
    "conditional_regularization": {
        "record_name": "NSBroadTubeConditionalRegularityTheoremReceipt",
        "canonical_name": "canonicalNSBroadTubeConditionalRegularityTheoremReceipt",
        "receipt_path": Path(
            "DASHI/Physics/Closure/NSBroadTubeConditionalRegularityTheoremReceipt.agda"
        ),
        "true_fields": (
            "conditionalRegularitySocketConstructed",
        ),
        "false_fields": (
            "promotionGateSatisfied",
            "unconditionalClayNS",
            "clayPromotion",
        ),
        "analytic_markers": {
            "composite_bkm_surface": {
                "composite_bkm_receipt_imported": {
                    "kind": "assigned_field",
                    "field": "broadTubeSerrinBKMCompositeReceipt",
                },
                "bkm_bridge_imported": {
                    "kind": "assigned_field",
                    "field": "broadTubeBKMBridgeReceipt",
                },
                "composite_route_constructed": {
                    "kind": "bool_field",
                    "field": "broadTubeCompositeRecorded",
                },
            }
        },
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
        "expose the remaining analytic proof obligations and proof-kernel markers explicitly."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "Fail closed on any missing receipt, missing true/false marker, or missing proof-"
        "kernel marker; no promotion claim is inferred from the receipts."
    ),
    "L": (
        "Read the four receipt surfaces, validate their recorded booleans and proof-"
        "kernel markers, derive the gate flags, and list the residual analytic obligations."
    ),
    "P": "FAIL_CLOSED_NS_BROAD_TUBE_CONDITIONAL_REGULARIZATION_SUMMARY",
    "G": "Clay promotion stays false and every gate remains explicitly conditional.",
    "F": (
        "The ledger is only valid when all four gates are true, Clay promotion is false, "
        "and the declared receipt and proof-kernel markers are present."
    ),
}

BOOL_LINE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(true|false)")
ASSIGNMENT_LINE = re.compile(r"^\s*[;{]?\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$")
FIELD_NAME_LINE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*$")


def _collect_expected_boolean_fields(spec: dict[str, Any]) -> list[str]:
    names: list[str] = list(spec["true_fields"]) + list(spec["false_fields"])
    seen: set[str] = set(names)
    for group_markers in spec.get("analytic_markers", {}).values():
        for marker_name, marker_spec in group_markers.items():
            if marker_spec["kind"] == "bool_field":
                field_name = marker_spec["field"]
                if field_name not in seen:
                    names.append(field_name)
                    seen.add(field_name)
    return names


def _extract_list_members(text: str, list_name: str) -> list[str] | None:
    lines = text.splitlines()
    collecting = False
    members: list[str] = []

    for raw_line in lines:
        stripped = raw_line.strip()
        if not collecting:
            if re.match(rf"^\s*{re.escape(list_name)}\s*=\s*$", raw_line):
                collecting = True
            continue

        if "[]" in stripped:
            return members

        match = re.match(r"^\s*(?:∷\s*)?([A-Za-z_][A-Za-z0-9_]*)\s*(?:∷)?\s*$", raw_line)
        if match:
            members.append(match.group(1))
            continue

        # Ignore blank lines while collecting a multi-line cons list.
        if stripped == "":
            continue

        # If a new top-level declaration starts before [], this is not a
        # standard complete list definition.
        if re.match(r"^[A-Za-z_][A-Za-z0-9_']*\s*:", stripped) or re.match(
            r"^(data|record|module|open|import)\b", stripped
        ):
            return members if members else None

    return None


def _extract_nat_constant(text: str, name: str) -> int | None:
    match = re.search(
        rf"^\s*{re.escape(name)}\s*=\s*\n\s*(\d+)\s*$",
        text,
        re.MULTILINE,
    )
    if match is None:
        return None
    return int(match.group(1))


def _extract_string_constant(text: str, name: str) -> str | None:
    match = re.search(
        rf"^\s*{re.escape(name)}\s*=\s*\n\s*\"([^\"]*)\"\s*$",
        text,
        re.MULTILINE,
    )
    if match is None:
        return None
    return match.group(1)


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


def _read_bool_fields(path: Path, fields: list[str]) -> dict[str, bool | None]:
    values: dict[str, bool | None] = {name: None for name in fields}
    text = path.read_text(encoding="utf-8")
    for match in BOOL_LINE.finditer(text):
        name, raw = match.group(1), match.group(2)
        if name in values:
            values[name] = raw == "true"
    return values


def _extract_record_fields(text: str, record_name: str) -> list[str]:
    fields: list[str] = []
    in_record = False
    in_field_block = False
    for raw_line in text.splitlines():
        line = raw_line.rstrip()
        stripped = line.strip()
        if not in_record:
            if re.match(rf"^record\s+{re.escape(record_name)}\s*:\s*.*\bwhere\s*$", stripped):
                in_record = True
            continue
        if not in_field_block:
            if stripped == "field":
                in_field_block = True
            continue
        if re.match(r"^(open|canonical|record|data|module)\b", stripped):
            break
        field_match = FIELD_NAME_LINE.match(line)
        if field_match:
            fields.append(field_match.group(1))
    return fields


def _extract_canonical_assignments(text: str, canonical_name: str) -> dict[str, str]:
    assignments: dict[str, str] = {}
    awaiting_record = False
    in_block = False
    for raw_line in text.splitlines():
        line = raw_line.rstrip()
        stripped = line.strip()
        if not in_block:
            if re.match(rf"^{re.escape(canonical_name)}\s*=\s*$", stripped):
                awaiting_record = True
                continue
            if awaiting_record and stripped == "record":
                in_block = True
                awaiting_record = False
                continue
            if re.match(rf"^{re.escape(canonical_name)}\s*=\s*record\b", stripped):
                in_block = True
            continue
        if stripped == "}":
            break
        match = ASSIGNMENT_LINE.match(line)
        if match:
            name = match.group(1)
            rhs = match.group(2).strip()
            assignments[name] = rhs
    return assignments


def _extract_analytic_markers(
    gate: str,
    spec: dict[str, Any],
    text: str,
    parsed_bools: dict[str, bool | None],
    canonical_assignments: dict[str, str],
    errors: list[str],
) -> dict[str, dict[str, bool | None]]:
    markers: dict[str, dict[str, bool | None]] = {}

    for group_name, group_spec in spec.get("analytic_markers", {}).items():
        group_values: dict[str, bool | None] = {}

        for marker_name, marker_spec in group_spec.items():
            kind = marker_spec["kind"]
            value: bool | None = None

            if kind == "bool_field":
                field_name = marker_spec["field"]
                value = parsed_bools.get(field_name)
                if value is None:
                    errors.append(
                        f"{gate}: missing required bool field for analytic marker {marker_name}: {field_name}"
                    )

            elif kind == "assigned_field":
                field_name = marker_spec["field"]
                value = field_name in canonical_assignments

            elif kind == "list_member":
                list_name = marker_spec["list_name"]
                member = marker_spec["member"]
                members = _extract_list_members(text, list_name)
                if members is None:
                    value = None
                    errors.append(
                        f"{gate}: unable to parse list members from {list_name} for marker {marker_name}"
                    )
                else:
                    value = member in members

            elif kind == "list_members":
                list_name = marker_spec["list_name"]
                required = set(marker_spec["members"])
                members = _extract_list_members(text, list_name)
                if members is None:
                    value = None
                    errors.append(
                        f"{gate}: unable to parse list members from {list_name} for marker {marker_name}"
                    )
                else:
                    value = required.issubset(set(members))

            elif kind == "string_contains":
                name = marker_spec["name"]
                needle = marker_spec["needle"]
                value_text = _extract_string_constant(text, name)
                if value_text is None:
                    value = None
                    errors.append(
                        f"{gate}: missing string constant {name} for analytic marker {marker_name}"
                    )
                else:
                    value = needle in value_text

            elif kind == "nat_pair":
                p_name = marker_spec["p_name"]
                q_name = marker_spec["q_name"]
                p_value = marker_spec["p_value"]
                q_value = marker_spec["q_value"]
                actual_p = _extract_nat_constant(text, p_name)
                actual_q = _extract_nat_constant(text, q_name)
                if actual_p is None or actual_q is None:
                    value = None
                    errors.append(
                        f"{gate}: missing nat constants for analytic marker {marker_name}: "
                        f"{p_name}={actual_p if actual_p is not None else 'None'}, {q_name}={actual_q if actual_q is not None else 'None'}"
                    )
                else:
                    value = (actual_p == p_value) and (actual_q == q_value)
            else:
                errors.append(
                    f"{gate}: unsupported analytic marker kind {kind!r} for {group_name}.{marker_name}"
                )

            group_values[marker_name] = value

        markers[group_name] = group_values

    return markers


def _evaluate_receipt(
    gate: str, spec: dict[str, Any], errors: list[str]
) -> dict[str, Any]:
    receipt_path = spec["receipt_path"]
    expected_bool_fields = _collect_expected_boolean_fields(spec)
    marker_values: dict[str, bool | None] = {name: None for name in expected_bool_fields}
    proof_kernel_markers: dict[str, bool | None] = {}
    declared_fields: list[str] = []
    assigned_fields: list[str] = []

    if not receipt_path.exists():
        errors.append(f"missing source receipt: {receipt_path}")
        return {
            "receipt_path": str(receipt_path),
            "gate_flag": False,
            "analytic_markers": {},
            "marker_values": marker_values,
            "proof_kernel_markers": proof_kernel_markers,
            "field_surface": {
                "declared_fields": declared_fields,
                "assigned_fields": assigned_fields,
                "missing_fields": [],
            },
        }

    text = receipt_path.read_text(encoding="utf-8")
    declared_fields = _extract_record_fields(text, spec["record_name"])
    canonical_assignments = _extract_canonical_assignments(text, spec["canonical_name"])
    assigned_fields = sorted(canonical_assignments)
    if not declared_fields:
        errors.append(f"{gate}: could not locate declared receipt field surface")
    if not canonical_assignments:
        errors.append(f"{gate}: could not locate canonical receipt instance")

    missing_fields = [name for name in declared_fields if name not in canonical_assignments]
    if missing_fields:
        errors.append(
            f"{gate}: missing receipt marker(s): {', '.join(missing_fields)}"
        )

    parsed = _read_bool_fields(receipt_path, expected_bool_fields)
    for name in marker_values:
        marker_values[name] = parsed.get(name)

    for name in declared_fields:
        proof_kernel_markers[f"{name}_assigned"] = name in canonical_assignments
    if declared_fields and not proof_kernel_markers:
        errors.append(f"{gate}: missing proof-kernel marker surface")

    true_mode = spec.get("true_mode", "all")
    if true_mode == "any":
        present_true_values = [
            marker_values.get(name)
            for name in spec["true_fields"]
            if marker_values.get(name) is not None
        ]
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

    analytic_markers = _extract_analytic_markers(
        gate, spec, text, parsed, canonical_assignments, errors
    )
    for group_name, group_values in analytic_markers.items():
        for marker_name, value in group_values.items():
            if value is not True:
                if value is None:
                    errors.append(
                        f"{gate}: missing analytic marker {group_name}.{marker_name}"
                    )
                else:
                    errors.append(
                        f"{gate}: analytic marker {group_name}.{marker_name} is false, expected true"
                    )

    if true_mode == "any":
        true_ok = any(marker_values.get(name) is True for name in spec["true_fields"])
    else:
        true_ok = all(marker_values.get(name) is True for name in spec["true_fields"])
    gate_flag = true_ok and all(marker_values.get(name) is False for name in spec["false_fields"])

    return {
        "receipt_path": str(receipt_path),
        "gate_flag": gate_flag,
        "analytic_markers": analytic_markers,
        "marker_values": marker_values,
        "proof_kernel_markers": proof_kernel_markers,
        "field_surface": {
            "declared_fields": declared_fields,
            "assigned_fields": assigned_fields,
            "missing_fields": missing_fields,
        },
    }


def _build_output(output_path: Path) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    receipts: dict[str, Any] = {}
    gate_flags: dict[str, bool] = {}
    remaining_obligations: dict[str, list[str]] = {}
    receipt_fields: dict[str, Any] = {}

    for gate, spec in RECEIPT_SPECS.items():
        result = _evaluate_receipt(gate, spec, errors)
        receipts[gate] = result
        gate_flags[gate] = bool(result["gate_flag"])
        remaining_obligations[gate] = list(spec["remaining_obligations"])
        receipt_fields[gate] = result["field_surface"]

    clay_promotion = False
    if not errors:
        warnings.append("all declared receipt markers were parsed and validated.")

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "status": "ok" if not errors else "error",
        "source_receipts": {
            gate: receipts[gate]["receipt_path"] for gate in RECEIPT_SPECS
        },
        "gate_flags": gate_flags,
        "receipt_markers": {gate: receipts[gate]["marker_values"] for gate in RECEIPT_SPECS},
        "analytic_marker_groups": {
            gate: receipts[gate]["analytic_markers"] for gate in RECEIPT_SPECS
        },
        "proof_kernel_markers": {
            gate: receipts[gate]["proof_kernel_markers"] for gate in RECEIPT_SPECS
        },
        "receipt_field_surface": receipt_fields,
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
