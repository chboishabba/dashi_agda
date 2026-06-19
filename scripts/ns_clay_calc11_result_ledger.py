#!/usr/bin/env python3
"""Emit the deterministic Calc 11 actual-result ledger."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


CONTRACT = "ns_clay_calc11_result_ledger"
VERSION = 1
DEFAULT_OUTPUT = Path("outputs") / f"{CONTRACT}.json"

CONTROL_CARD = {
    "O": "Worker 2 owns the Calc 11 actual-result Python ledger and its tests.",
    "R": "Record the completed Calc 11 result with deterministic JSON and reject tampering.",
    "C": "A stdlib CLI emits one JSON payload, hashes it canonically, and validates the payload before exit.",
    "S": "This is an empirical result ledger, not a promotion claim.",
    "L": "result -> decision -> implications -> non_promotion -> parity_hash -> validation.",
    "P": "Use the result as a non-promoting record for downstream checks.",
    "G": "Validation passes only when the payload matches the fixed Calc 11 result and non-promotion state.",
    "F": "The ledger explicitly records no special alignment and no clay promotion.",
}

RESULT = {
    "bottom_5_percent_g12_mean_omega_e2_fraction": 0.343,
    "random_baseline": 1.0 / 3.0,
    "full_boundary_layer_mean": 0.432,
    "max": 1.0,
    "max_omega_e2_fraction": 1.0,
    "percentile_distribution": "isolated/scattered across percentiles",
    "monotone_increase_as_g12_decreases": False,
}

DECISION = "no_special_alignment"

IMPLICATIONS = {
    "special_alignment_supported": False,
    "summary": "The Calc 11 result stays close to the random baseline and does not show a monotone low-g12 lift.",
}

NON_PROMOTION = {
    "clay_promotion": False,
}

OUTPUT_SCHEMA = {
    "type": "object",
    "required_keys": [
        "contract",
        "version",
        "control_card",
        "result",
        "decision",
        "implications",
        "non_promotion",
        "parity_hash",
        "validation_passed",
    ],
    "control_card_keys": ["O", "R", "C", "S", "L", "P", "G", "F"],
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_payload() -> dict[str, Any]:
    payload = {
        "contract": CONTRACT,
        "version": VERSION,
        "control_card": dict(CONTROL_CARD),
        "result": dict(RESULT),
        "decision": DECISION,
        "implications": dict(IMPLICATIONS),
        "non_promotion": dict(NON_PROMOTION),
        "parity_hash": "",
        "validation_passed": False,
    }
    payload["parity_hash"] = stable_hash(
        {k: v for k, v in payload.items() if k not in {"parity_hash", "validation_passed"}}
    )
    payload["validation_passed"] = validate_payload({**payload, "validation_passed": True})
    return payload


def validate_payload(payload: dict[str, Any]) -> bool:
    if not isinstance(payload, dict):
        return False
    if payload.get("contract") != CONTRACT:
        return False
    if payload.get("version") != VERSION:
        return False

    required_keys = OUTPUT_SCHEMA["required_keys"]
    if not all(key in payload for key in required_keys):
        return False

    control_card = payload.get("control_card")
    if not isinstance(control_card, dict) or set(control_card) != set(OUTPUT_SCHEMA["control_card_keys"]):
        return False
    if control_card != CONTROL_CARD:
        return False

    result = payload.get("result")
    if not isinstance(result, dict):
        return False
    if set(result) != set(RESULT):
        return False
    if result["bottom_5_percent_g12_mean_omega_e2_fraction"] != 0.343:
        return False
    if result["random_baseline"] != 1.0 / 3.0:
        return False
    if result["full_boundary_layer_mean"] != 0.432:
        return False
    if result["max"] != 1.0:
        return False
    if result["max_omega_e2_fraction"] != 1.0:
        return False
    if result["percentile_distribution"] != "isolated/scattered across percentiles":
        return False
    if result["monotone_increase_as_g12_decreases"] is not False:
        return False

    if payload.get("decision") != DECISION:
        return False

    implications = payload.get("implications")
    if not isinstance(implications, dict):
        return False
    if implications.get("special_alignment_supported") is not False:
        return False

    non_promotion = payload.get("non_promotion")
    if not isinstance(non_promotion, dict):
        return False
    if non_promotion.get("clay_promotion") is not False:
        return False

    parity_hash = payload.get("parity_hash")
    if not isinstance(parity_hash, str) or len(parity_hash) != 64:
        return False
    try:
        int(parity_hash, 16)
    except ValueError:
        return False

    expected_hash = stable_hash(
        {k: v for k, v in payload.items() if k not in {"parity_hash", "validation_passed"}}
    )
    if parity_hash != expected_hash:
        return False

    if payload.get("validation_passed") is not True:
        return False

    return True


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    payload = build_payload()
    if not validate_payload(payload):
        print("payload validation failed", file=sys.stderr)
        return 1
    write_json(args.output, payload)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
