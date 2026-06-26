#!/usr/bin/env python3
"""Emit the deterministic Calc 11 vorticity/e2-projection ledger/spec."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


CONTRACT = "ns_clay_calc11_vorticity_projection_ledger"
CALC_ID = 11
CALC_NAME = "vorticity_e2_projection_boundary_layer"
DEFAULT_OUTPUT = Path("outputs") / f"{CONTRACT}.json"

CONTROL_CARD = {
    "O": "Worker 3 owns the Calc 11 vorticity/e2-projection ledger only.",
    "R": "Record the required inputs, omega_e2_fraction formula, thresholds, output schema, and non-promotion flags.",
    "C": "A deterministic Python stdlib CLI emits one JSON ledger and validates the payload before exit.",
    "S": "This calc is a specification surface, not a data pipeline or a theorem proof.",
    "L": "inputs -> formula -> thresholds -> schema -> validated non-promotion payload.",
    "P": "Use the ledger as a contract for downstream checks, not as a promotion certificate.",
    "G": "Validation passes only when the payload matches the declared schema and every non-promotion flag stays false.",
    "F": "No Clay or Navier-Stokes promotion is emitted by this calc.",
}

REQUIRED_INPUTS: tuple[dict[str, Any], ...] = (
    {
        "name": "velocity_field",
        "symbol": "u",
        "role": "primary NS input",
        "required": True,
        "shape": "vector_field",
        "description": "Velocity field used to form vorticity and the strain tensor.",
    },
    {
        "name": "vorticity_field",
        "symbol": "omega",
        "role": "derived from curl(u)",
        "required": True,
        "shape": "vector_field",
        "description": "Vorticity field used in |<omega,e2>|^2 / |omega|^2.",
    },
    {
        "name": "strain_eigenframe",
        "symbol": "e1_e2_e3",
        "role": "eigenvectors of S = sym(grad u)",
        "required": True,
        "shape": "orthonormal_frame",
        "description": "Strain eigenvectors e1/e2/e3; e2 is the null-strain direction monitored on the boundary layer.",
    },
    {
        "name": "boundary_layer_mask",
        "symbol": "layer_delta_C",
        "role": "boundary-layer restriction near partial Omega_K",
        "required": True,
        "shape": "boolean_grid",
        "description": "Cells belonging to the selected carrier boundary layer.",
    },
    {
        "name": "gap_field",
        "symbol": "g12",
        "role": "strain eigengap diagnostic",
        "required": True,
        "shape": "scalar_grid",
        "description": "Boundary-layer gap field used to report min_g12.",
    },
)

FORMULA = {
    "name": "omega_e2_fraction",
    "expression": "omega_e2_fraction = |<omega,e2>|^2 / max(|omega|^2, eps)",
    "symbols": {
        "omega_e2_fraction": "fraction of local vorticity energy in the e2 eigenvector direction",
        "omega": "vorticity field",
        "e2": "middle strain eigenvector / null-strain direction on partial Omega_K",
        "eps": "positive tolerance floor",
    },
    "interpretation": (
        "The calc tests whether vorticity concentrates in the null-strain e2 "
        "direction near the tightest boundary-layer gap cells, while preserving "
        "a fail-closed stance."
    ),
}

DECISION_THRESHOLDS = {
    "omega_e2_fraction_low": 0.1,
    "omega_e2_fraction_random": 1.0 / 3.0,
    "omega_e2_fraction_high": 0.9,
    "promotion_margin_min": 1.0,
    "non_promotion_required": True,
}

OUTPUT_FIELDS: tuple[dict[str, Any], ...] = (
    {
        "name": "mean_omega_e2_fraction",
        "type": "float",
        "description": "Mean |<omega,e2>|^2/|omega|^2 over boundary-layer cells.",
    },
    {
        "name": "max_omega_e2_fraction",
        "type": "float",
        "description": "Maximum |<omega,e2>|^2/|omega|^2 over boundary-layer cells.",
    },
    {
        "name": "layer_cell_count",
        "type": "int",
        "description": "Number of boundary-layer cells sampled.",
    },
    {
        "name": "min_g12",
        "type": "float",
        "description": "Minimum g12 over the sampled boundary-layer cells.",
    },
)

NON_PROMOTION_FLAGS = {
    "clay_navier_stokes_promoted": False,
    "clayNavierStokesPromoted": False,
    "full_clay_ns_solved": False,
    "fullClayNSSolved": False,
    "promotion_allowed": False,
    "proof_claimed": False,
}

OUTPUT_SCHEMA = {
    "type": "object",
    "required_keys": [
        "contract",
        "calc_id",
        "calc_name",
        "required_inputs",
        "formula",
        "decision_thresholds",
        "output_fields",
        "non_promotion_flags",
        "validation_passed",
        "ledger_hash",
    ],
    "required_inputs_schema": {
        "type": "array",
        "item_keys": ["name", "symbol", "role", "required", "shape", "description"],
    },
    "formula_schema": {
        "type": "object",
        "required_keys": ["name", "expression", "symbols", "interpretation"],
    },
    "threshold_schema": {
        "type": "object",
        "required_keys": [
            "omega_e2_fraction_low",
            "omega_e2_fraction_random",
            "omega_e2_fraction_high",
            "promotion_margin_min",
            "non_promotion_required",
        ],
    },
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_payload() -> dict[str, Any]:
    payload = {
        "contract": CONTRACT,
        "calc_id": CALC_ID,
        "calc_name": CALC_NAME,
        "required_inputs": [dict(item) for item in REQUIRED_INPUTS],
        "formula": dict(FORMULA),
        "decision_thresholds": dict(DECISION_THRESHOLDS),
        "output_fields": [dict(item) for item in OUTPUT_FIELDS],
        "output_schema": dict(OUTPUT_SCHEMA),
        "non_promotion_flags": dict(NON_PROMOTION_FLAGS),
        "control_card": dict(CONTROL_CARD),
        "validation_passed": True,
        "ledger_hash": "",
    }
    payload["ledger_hash"] = stable_hash({k: v for k, v in payload.items() if k != "ledger_hash"})
    payload["validation_passed"] = validate_payload(payload)
    return payload


def validate_payload(payload: dict[str, Any]) -> bool:
    required_keys = OUTPUT_SCHEMA["required_keys"]
    if not isinstance(payload, dict):
        return False
    if payload.get("contract") != CONTRACT:
        return False
    if payload.get("calc_id") != CALC_ID or payload.get("calc_name") != CALC_NAME:
        return False
    if not all(key in payload for key in required_keys):
        return False
    ledger_hash = payload.get("ledger_hash")
    if not isinstance(ledger_hash, str) or len(ledger_hash) != 64:
        return False
    try:
        int(ledger_hash, 16)
    except ValueError:
        return False

    required_inputs = payload.get("required_inputs")
    if not isinstance(required_inputs, list) or len(required_inputs) != len(REQUIRED_INPUTS):
        return False
    expected_input_keys = set(OUTPUT_SCHEMA["required_inputs_schema"]["item_keys"])
    for item in required_inputs:
        if not isinstance(item, dict) or set(item.keys()) != expected_input_keys:
            return False
        if item.get("required") is not True:
            return False
        if not all(item.get(field) for field in ("name", "symbol", "role", "shape", "description")):
            return False

    formula = payload.get("formula")
    if not isinstance(formula, dict) or set(formula.keys()) != set(
        OUTPUT_SCHEMA["formula_schema"]["required_keys"]
    ):
        return False
    if not formula.get("expression") or not formula.get("interpretation"):
        return False
    symbols = formula.get("symbols")
    if not isinstance(symbols, dict) or not {
        "omega_e2_fraction",
        "omega",
        "e2",
        "eps",
    } <= set(symbols):
        return False

    thresholds = payload.get("decision_thresholds")
    if not isinstance(thresholds, dict) or set(thresholds.keys()) != set(
        OUTPUT_SCHEMA["threshold_schema"]["required_keys"]
    ):
        return False
    if thresholds["omega_e2_fraction_low"] != 0.1:
        return False
    if thresholds["omega_e2_fraction_random"] != 1.0 / 3.0:
        return False
    if thresholds["omega_e2_fraction_high"] != 0.9:
        return False
    if thresholds["promotion_margin_min"] != 1.0:
        return False
    if thresholds["non_promotion_required"] is not True:
        return False

    output_fields = payload.get("output_fields")
    if not isinstance(output_fields, list) or len(output_fields) != len(OUTPUT_FIELDS):
        return False
    if [item.get("name") for item in output_fields] != [item["name"] for item in OUTPUT_FIELDS]:
        return False

    non_promotion_flags = payload.get("non_promotion_flags")
    if not isinstance(non_promotion_flags, dict) or not non_promotion_flags:
        return False
    if any(value is not False for value in non_promotion_flags.values()):
        return False

    control_card = payload.get("control_card")
    if not isinstance(control_card, dict):
        return False
    if set(control_card.keys()) != {"O", "R", "C", "S", "L", "P", "G", "F"}:
        return False

    return True


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    _repo_root = args.repo_root.resolve()
    payload = build_payload()
    if not validate_payload(payload):
        print("payload validation failed", file=sys.stderr)
        return 1
    write_json(args.json_output, payload)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
