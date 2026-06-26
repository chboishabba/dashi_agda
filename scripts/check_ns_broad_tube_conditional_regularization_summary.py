#!/usr/bin/env python3
"""Validate the broad-tube conditional regularization summary payload."""

from __future__ import annotations

import argparse
import json
import re
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
ANALYTIC_MARKER_KEYS = (
    "analytic_marker_groups",
    "analytic_content_markers",
    "analytic_markers",
    "analytic_content",
    "receipt_markers",
)

ANALYTIC_MARKER_CHECKS = {
    "nondegenerate_gradient": [
        {
            "label": "coarea nondegeneracy is recorded almost everywhere",
            "alternatives": (
                ("coareaNondegeneracyAERecorded", True),
                ("coareaNondegeneracyAERecordedIsTrue", True),
                ("coarea_nondegeneracy_ae_recorded", True),
            ),
        },
        {
            "label": "pointwise-gradient theorem is blocked",
            "alternatives": (
                ("unconditionalLambda2GradientTheorem", False),
                ("unconditionalLambda2GradientTheoremIsFalse", False),
                ("pointwiseLowerBoundNeedsNonFlatNoCriticalManifold", True),
                ("pointwiseLowerBoundNeedsNonFlatNoCriticalManifoldIsTrue", True),
                ("pointwise_blocker_required", True),
            ),
        },
    ],
    "vorticity_coverage": [
        {
            "label": "vorticity coverage remains conditional",
            "alternatives": (
                ("assumptionsDischarged", False),
                ("assumptionsDischargedIsFalse", True),
            ),
        },
        {
            "label": "vorticity coverage socket is recorded",
            "alternatives": (
                ("coverageSocketConstructed", True),
                ("coverageSocketConstructedIsTrue", True),
            ),
        },
    ],
    "serrin_exponent_discharge": [
        {
            "label": "Serrin exponent socket is recorded",
            "alternatives": (
                ("serrinExponentSocketConstructed", True),
                ("serrinExponentSocketConstructedIsTrue", True),
                ("serrin_exponent_socket_constructed", True),
            ),
        },
        {
            "label": "unconditional Serrin route is blocked",
            "alternatives": (
                ("unconditionalSerrinBound", False),
                ("unconditionalSerrinBoundIsFalse", False),
            ),
        },
        {
            "label": "admissible Serrin pair (8,4) is recorded",
            "custom": "serrin_pair",
        },
    ],
    "conditional_regularization": [
        {
            "label": "final BKM route dependencies are recorded",
            "alternatives": (
                ("broadTubeBKMBridgeReceipt", True),
                ("broadTubeBKMBridgeReceiptIsTrue", True),
                ("broadTubeSerrinBKMCompositeReceipt", True),
                ("broadTubeSerrinBKMCompositeReceiptIsTrue", True),
                ("composite_bkm_receipt_imported", True),
                ("bkm_bridge_imported", True),
            ),
        },
        {
            "label": "Q2-GD1 route and BKM dependencies are recorded",
            "custom": "q2_gd1_route",
        },
        {
            "label": "conditional route dependencies remain open and unpromoted",
            "alternatives": (
                ("unconditionalClayNS", False),
                ("unconditionalClayNSIsFalse", False),
                ("promotionGateSatisfied", False),
                ("promotionGateSatisfiedIsFalse", False),
                ("clayPromotion", False),
                ("clayPromotionIsFalse", False),
            ),
        },
        {
            "label": "conditional regularity socket is recorded",
            "alternatives": (
                ("conditionalRegularitySocketConstructed", True),
                ("conditionalRegularitySocketConstructedIsTrue", True),
            ),
        },
    ],
}

CONTROL_CARD = {
    "O": "Owner 5 validates the broad-tube conditional regularization summary fields.",
    "R": "Fail-closed validation that gate status, promotion suppression, proof-kernel markers, and obligation reporting are explicit.",
    "C": SCRIPT_NAME,
    "S": (
        "A summary is accepted only if it records four true gates, Clay promotion false, "
        "declared receipt and proof-kernel markers, and a stable residual-obligation surface."
    ),
    "L": (
        "Load the summary JSON, validate the gate set, marker surfaces, and promotion "
        "flags, and emit a canonical checker receipt."
    ),
    "P": "FAIL_CLOSED_NS_BROAD_TUBE_CONDITIONAL_REGULARIZATION_SUMMARY",
    "G": "No route, theorem, or Clay promotion is inferred by this checker.",
    "F": "Only an explicit conditional-summary ledger can pass; missing gates or markers fail validation.",
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


def _coerce_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        if value in (0, 1):
            return value == 1
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in {"true", "1", "yes", "on"}:
            return True
        if normalized in {"false", "0", "no", "off"}:
            return False
    return None


def _normalize_name(name: str) -> str:
    return name.replace("-", "_")


def _normalize_marker_entries(
    entries: Any,
    *,
    prefix: str = "",
) -> dict[str, Any]:
    normalized: dict[str, Any] = {}

    def emit(key: str, value: Any) -> None:
        normalized[key] = value
        normalized[_normalize_name(key)] = value
        if "." in key:
            base = key.split(".")[-1]
            normalized.setdefault(base, value)
            normalized.setdefault(_normalize_name(base), value)

    def emit_nested(key: str, value: Any) -> None:
        if isinstance(value, (dict, list)):
            normalized.update(_normalize_marker_entries(value, prefix=key))
            return
        emit(key, value)

    if isinstance(entries, dict):
        for name, value in entries.items():
            key = str(name)
            emit_nested(key if not prefix else f"{prefix}.{key}", value)
        return normalized
    if not isinstance(entries, list):
        raise TypeError("marker group must be dict or list")

    for item in entries:
        if isinstance(item, str):
            text = item.strip()
            if not text:
                continue
            match = re.match(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:[:=]\s*(.+))?\s*$", text)
            if match is None:
                emit(text if not prefix else f"{prefix}.{text}", True)
                continue
            name = match.group(1)
            if match.group(2) is None:
                emit(name if not prefix else f"{prefix}.{name}", True)
                continue
            value = match.group(2).strip().strip('"\'')
            bool_value = _coerce_bool(value)
            value = bool_value if bool_value is not None else value
            emit(name if not prefix else f"{prefix}.{name}", value)
            continue

        if isinstance(item, dict):
            if not item:
                continue
            name = item.get("name")
            if isinstance(name, str):
                marker_value = item.get("value", item.get("present", item.get("state", True)))
                emit_nested(name if not prefix else f"{prefix}.{name}", marker_value)
                continue

            if len(item) == 1:
                marker_name, marker_value = next(iter(item.items()))
                emit_nested(
                    str(marker_name) if not prefix else f"{prefix}.{marker_name}",
                    marker_value,
                )
                continue

            # Nested marker bundles: {"group": {...}} or {"group": [ ... ]}.
            for marker_name, marker_value in item.items():
                emit_nested(
                    str(marker_name) if not prefix else f"{prefix}.{marker_name}",
                    marker_value,
                )

        # Ignore non-dict/str list members (e.g., null) instead of silently masking structure.
        continue

    return normalized


def _select_analytic_markers(payload: dict[str, Any], errors: list[str]) -> tuple[dict[str, Any], str] | tuple[None, None]:
    selected: Any = None
    source = None
    for key in ANALYTIC_MARKER_KEYS:
        if key not in payload:
            continue
        selected = payload.get(key)
        source = key
        if isinstance(selected, (dict, list)):
            if isinstance(selected, dict):
                # Keep top-level per-gate keys; normalize per-gate content later.
                return {str(gate): values for gate, values in selected.items()}, key
            return _normalize_marker_entries(selected), key
        _record_error(errors, f"{key} must be a dict or list")
        selected = None
        source = None
        continue

    return None, None


def _normalize_analyses(value: Any, gate: str, source: str, errors: list[str]) -> dict[str, Any] | None:
    if not isinstance(value, (dict, list)):
        _record_error(
            errors,
            f"{source}[{gate}] must be a dict or list of analytic markers",
        )
        return None
    normalized = _normalize_marker_entries(value, prefix=str(gate))
    if not normalized:
        _record_error(errors, f"{source}[{gate}] must not be empty")
        return None

    # Keep compact marker keys available for callers that use unqualified names.
    # Prefix normalization for nested groups preserves both qualified and unqualified keys.
    for key, value in list(normalized.items()):
        if key.startswith(f"{gate}."):
            short = key[len(f"{gate}.") :]
            if short:
                normalized.setdefault(short, value)
    return normalized


def _marker_alt_satisfied(markers: dict[str, Any], alternatives: tuple[tuple[str, bool], ...]) -> bool:
    for name, expected in alternatives:
        candidates = {
            name,
            name.lower(),
            _normalize_name(name),
            _normalize_name(name).lower(),
        }
        found: list[Any] = []
        for key, value in markers.items():
            key_norm = str(key)
            key_norm_l = key_norm.lower()
            base = str(key).split(".")[-1]
            base_candidates = {
                base,
                base.lower(),
                _normalize_name(base),
                _normalize_name(base).lower(),
            }
            if key in candidates or key_norm in candidates or key_norm_l in candidates or base in candidates or base.lower() in candidates:
                found.append(value)
                continue
            if any(key_norm_l == c for c in candidates) or any(key_norm_l.endswith("." + c) for c in candidates):
                found.append(value)
        for actual in found:
            coerced = _coerce_bool(actual)
            if coerced is not None and coerced == expected:
                return True
    return False


def _has_serrin_pair_84(markers: dict[str, Any]) -> bool:
    strong_names = (
        "serrinAdmissibleP",
        "serrinAdmissibleQ",
        "serrinTimeExponentField",
        "serrinSpaceExponentField",
        "serrinExactRelationField",
        "serrinRelationMarkerField",
        "serrinRelationFieldLabels",
        "serrinRelationFields",
        "serrinExactRelation",
        "serrinPair84Recorded",
        "serrinPair_8_4_recorded",
        "serrin_pair_8_4_recorded",
        "serrin_pair_8_4",
        "serrin_pair",
    )
    for name in strong_names:
        value = markers.get(name)
        if _coerce_bool(value) is True:
            return True
        value2 = markers.get(f"{name}.")
        if _coerce_bool(value2) is True:
            return True
        if isinstance(value, str):
            lower = value.lower().replace(" ", "")
            if (
                "2/8+3/4=1" in lower
                or "2/p+3/q=1" in lower
                or "(8,4)" in lower
                or "8,4" in lower
            ):
                return True
        if isinstance(value2, str):
            lower = value2.lower().replace(" ", "")
            if (
                "2/8+3/4=1" in lower
                or "2/p+3/q=1" in lower
                or "(8,4)" in lower
                or "8,4" in lower
            ):
                return True

    for name, value in markers.items():
        text = f"{name} {value}".lower().replace(" ", "")
        if "2/8+3/4=1" in text or "2/p+3/q=1" in text or "(8,4)" in text:
            return True
        if "8,4" in text and ("serrin" in text or "pair" in text or "p" in text or "q" in text):
            if _coerce_bool(value) is not False:
                return True
        if isinstance(value, (list, tuple)) and len(value) >= 2:
            if _coerce_bool(value[0]) is None and _coerce_bool(value[1]) is None:
                try:
                    if int(value[0]) == 8 and int(value[1]) == 4:
                        return True
                except (TypeError, ValueError):
                    pass
        if isinstance(value, dict):
            p = value.get("p", value.get("P"))
            q = value.get("q", value.get("Q"))
            try:
                if p is not None and q is not None and int(p) == 8 and int(q) == 4:
                    return True
            except (TypeError, ValueError):
                pass

    p_candidates = {
        "serrinadmissiblep",
        "serrindemandsp",
        "admissiblep",
        "serrinpairp",
        "serrinp",
        "p",
    }
    q_candidates = {
        "serrinadmissibleq",
        "admissibleq",
        "serrinpairq",
        "serrinq",
        "q",
    }

    p = None
    q = None
    for key, value in markers.items():
        if not isinstance(value, int):
            continue
        normalized_key = _normalize_name(str(key).lower())
        if normalized_key in p_candidates and p is None:
            p = value
        if normalized_key in q_candidates and q is None:
            q = value
    if p is not None and q is not None and p == 8 and q == 4:
        return True

    return False


def _has_q2_gd1_route(markers: dict[str, Any]) -> bool:
    q2_ok = False
    gd1_ok = False
    bkm_ok = False

    for raw_name, value in markers.items():
        coerced = _coerce_bool(value)
        if coerced is not True:
            continue

        name = str(raw_name).lower()
        norm = _normalize_name(name)

        if "bkm" in norm and ("bridge" in norm or "composite" in norm or "receipt" in norm):
            bkm_ok = True
        if "q2" in norm and "required" in norm:
            q2_ok = True
        if "gd1" in norm and "required" in norm:
            gd1_ok = True
        if "q2receipt" in norm:
            q2_ok = True
        if "gd1receipt" in norm:
            gd1_ok = True
        if "q2_gd1" in norm and ("route" in norm or "recorded" in norm):
            q2_ok = True
            gd1_ok = True
        if "theoremgq2gd1chainrecorded" in norm or "theoremg_q2_gd1_chain_recorded" in norm:
            q2_ok = True
            gd1_ok = True

        if not bkm_ok and ("q2_gd1" in norm or "q2gd1" in norm) and "recorded" in norm:
            bkm_ok = True
        if not bkm_ok and ("theoremgq2gd1chainrecorded" in norm or "theoremg_q2_gd1_chain_recorded" in norm):
            bkm_ok = True

    return q2_ok and gd1_ok and bkm_ok


def _validate_analytic_markers(payload: dict[str, Any], errors: list[str]) -> None:
    marker_groups, marker_source = _select_analytic_markers(payload, errors)
    if marker_groups is None:
        _record_error(
            errors,
            "missing analytic marker group (expected one of analytic_content_markers, analytic_markers, receipt_markers)",
        )
        return

    if not isinstance(marker_groups, dict):
        _record_error(errors, f"{marker_source} must be a dict keyed by gate id")
        return

    missing_gate_markers = [gate for gate in EXPECTED_GATES if gate not in marker_groups]
    if missing_gate_markers:
        _record_error(
            errors,
            f"{marker_source} missing gates: {', '.join(missing_gate_markers)}",
        )
    for gate in EXPECTED_GATES:
        if gate not in marker_groups:
            continue
        gate_markers = _normalize_analyses(marker_groups.get(gate), gate, marker_source, errors)
        if gate_markers is None:
            continue
        for aux_key in ("receipt_markers", "proof_kernel_markers"):
            aux_groups = payload.get(aux_key)
            if isinstance(aux_groups, dict) and gate in aux_groups:
                aux_markers = _normalize_analyses(aux_groups.get(gate), gate, aux_key, errors)
                if aux_markers is not None:
                    gate_markers.update(aux_markers)

        checks = ANALYTIC_MARKER_CHECKS.get(gate, [])
        for check in checks:
            label = check["label"]
            alternatives = check.get("alternatives")
            if alternatives is not None:
                if not _marker_alt_satisfied(gate_markers, tuple(alternatives)):  # type: ignore[arg-type]
                    names = ", ".join(name for name, _ in alternatives)  # type: ignore[misc]
                    _record_error(
                        errors,
                        f"{marker_source}[{gate}] missing expected {label}: one of {names} with required boolean",
                    )
                continue
            if check.get("custom") == "serrin_pair":
                if not _has_serrin_pair_84(gate_markers):
                    _record_error(
                        errors,
                        f"{marker_source}[{gate}] missing expected Serrin admissible pair (8,4) evidence",
                    )
            elif check.get("custom") == "q2_gd1_route":
                if not _has_q2_gd1_route(gate_markers):
                    _record_error(
                        errors,
                        f"{marker_source}[{gate}] missing expected Q2-GD1 route and BKM evidence",
                    )


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

    receipt_markers = payload.get("receipt_markers")
    if not isinstance(receipt_markers, dict):
        _record_error(errors, "missing or invalid receipt_markers dict")
    else:
        missing_marker_gates = [gate for gate in EXPECTED_GATES if gate not in receipt_markers]
        extra_marker_gates = sorted(set(receipt_markers) - set(EXPECTED_GATES))
        if missing_marker_gates:
            _record_error(errors, f"missing receipt marker gates: {', '.join(missing_marker_gates)}")
        if extra_marker_gates:
            _record_error(errors, f"unexpected receipt marker gates: {', '.join(extra_marker_gates)}")
        for gate in EXPECTED_GATES:
            if gate not in receipt_markers:
                continue
            gate_markers = receipt_markers.get(gate)
            if not isinstance(gate_markers, dict):
                _record_error(errors, f"receipt_markers[{gate}] must be a dict")
                continue
            if not gate_markers:
                _record_error(errors, f"receipt_markers[{gate}] must not be empty")
            missing_values = sorted(name for name, value in gate_markers.items() if value is None)
            if missing_values:
                _record_error(
                    errors,
                    f"receipt_markers[{gate}] has missing markers: {', '.join(missing_values)}",
                )

    proof_kernel_markers = payload.get("proof_kernel_markers")
    if not isinstance(proof_kernel_markers, dict):
        _record_error(errors, "missing or invalid proof_kernel_markers dict")
    else:
        missing_proof_gates = [gate for gate in EXPECTED_GATES if gate not in proof_kernel_markers]
        extra_proof_gates = sorted(set(proof_kernel_markers) - set(EXPECTED_GATES))
        if missing_proof_gates:
            _record_error(errors, f"missing proof-kernel marker gates: {', '.join(missing_proof_gates)}")
        if extra_proof_gates:
            _record_error(errors, f"unexpected proof-kernel marker gates: {', '.join(extra_proof_gates)}")
        for gate in EXPECTED_GATES:
            if gate not in proof_kernel_markers:
                continue
            gate_proofs = proof_kernel_markers.get(gate)
            if not isinstance(gate_proofs, dict):
                _record_error(errors, f"proof_kernel_markers[{gate}] must be a dict")
                continue
            if not gate_proofs:
                _record_error(errors, f"proof_kernel_markers[{gate}] must not be empty")
            invalid = sorted(name for name, value in gate_proofs.items() if value is not True)
            if invalid:
                _record_error(
                    errors,
                    f"proof_kernel_markers[{gate}] must set all markers true: {', '.join(invalid)}",
                )

    receipt_field_surface = payload.get("receipt_field_surface")
    if not isinstance(receipt_field_surface, dict):
        _record_error(errors, "missing or invalid receipt_field_surface dict")
    else:
        missing_surface_gates = [gate for gate in EXPECTED_GATES if gate not in receipt_field_surface]
        extra_surface_gates = sorted(set(receipt_field_surface) - set(EXPECTED_GATES))
        if missing_surface_gates:
            _record_error(errors, f"missing receipt field surfaces: {', '.join(missing_surface_gates)}")
        if extra_surface_gates:
            _record_error(errors, f"unexpected receipt field surfaces: {', '.join(extra_surface_gates)}")
        for gate in EXPECTED_GATES:
            if gate not in receipt_field_surface:
                continue
            surface = receipt_field_surface.get(gate)
            if not isinstance(surface, dict):
                _record_error(errors, f"receipt_field_surface[{gate}] must be a dict")
                continue
            declared = surface.get("declared_fields")
            assigned = surface.get("assigned_fields")
            missing = surface.get("missing_fields")
            if not isinstance(declared, list):
                _record_error(errors, f"receipt_field_surface[{gate}].declared_fields must be a list")
            if not isinstance(assigned, list):
                _record_error(errors, f"receipt_field_surface[{gate}].assigned_fields must be a list")
            if not isinstance(missing, list):
                _record_error(errors, f"receipt_field_surface[{gate}].missing_fields must be a list")
            elif missing:
                _record_error(errors, f"receipt_field_surface[{gate}] has missing markers: {', '.join(missing)}")
            if isinstance(declared, list) and isinstance(assigned, list):
                if not declared:
                    _record_error(errors, f"receipt_field_surface[{gate}].declared_fields must not be empty")
                if not assigned:
                    _record_error(errors, f"receipt_field_surface[{gate}].assigned_fields must not be empty")
                missing_declared = [name for name in declared if name not in assigned]
                if missing_declared:
                    _record_error(
                        errors,
                        f"receipt_field_surface[{gate}] omits declared fields: {', '.join(missing_declared)}",
                    )

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

    _validate_analytic_markers(payload, errors)

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
        "proof_kernel_markers": payload.get("proof_kernel_markers") if payload is not None else None,
        "promotion_flags": payload.get("promotion_flags") if payload is not None else None,
        "receipt_field_surface": payload.get("receipt_field_surface") if payload is not None else None,
    }

    output_path = args.output_json if args.output_json is not None else None
    if output_path is not None:
        _write_json(output_path, result, pretty=args.pretty)

    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
