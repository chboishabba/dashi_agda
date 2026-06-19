#!/usr/bin/env python3
"""Emit a deterministic post-Calc-11 Navier-Stokes Clay summary ledger."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


CONTRACT = "ns_clay_post_calc11_summary"
VERSION = 1
DEFAULT_OUTPUT = Path("outputs") / f"{CONTRACT}.json"

CONTROL_CARD = {
    "O": "Worker 5 owns the post-Calc-11 NS Clay summary ledger.",
    "R": (
        "Record post-Calc-11 state fields, the Calc12 optional route selector,"
        " closeable-package summary, remaining hard walls, and non-promotion"
        " checks in one fail-closed JSON ledger."
    ),
    "C": "A deterministic Python stdlib CLI emits canonical JSON and validates it before exit.",
    "S": "The lane is governance/status reporting, not proof production.",
    "L": (
        "post_calc11 -> calc12_route_selector -> closeable_packages"
        " -> remaining_hard_walls -> non_promotion -> parity_hash -> validation"
    ),
    "P": "Use the ledger as a checkpoint summary for downstream non-promoting checks; Calc12 stays optional.",
    "G": (
        "Validation passes only when calc11 is marked complete/no_special_alignment,"
        " Calc12 remains an optional non-blocking route selector, no further calcs"
        " are blocking, the closeable package list is exact (7), remaining hard"
        " walls are unchanged, and no theorem/clay promotion is true."
    ),
    "F": (
        "No theorem promotion, no Clay promotion, proof_blocking False, and"
        " no_further_calcs_blocking True are encoded as explicit fields."
    ),
    "calc12_route_selector": {
        "calc": "Calc12",
        "route_selector": "statistical",
        "power_law": "|<omega,e2>|^2 ~ C*g12^beta",
        "beta_decision_thresholds": {
            ">1": "regularity_consistent",
            "<1": "blowup_precursor",
            "CI straddles 1": "inconclusive",
        },
        "proof_blocking": False,
        "no_further_calcs_blocking": True,
    },
    "optional_next_calc_blocks_proof": False,
    "proof_blocking": False,
    "no_further_calcs_blocking": True,
}

CLOSEABLE_PACKAGES: tuple[str, ...] = (
    "millerToH5",
    "GD3-SobolevBound-Correct",
    "coareaGradientBound",
    "LocalConcentration",
    "pigeon_concentration",
    "StepA_PerComponent",
    "BoundaryHB_Correct",
)

REMNANT_HARD_WALLS: tuple[str, ...] = ("KornLevelSet", "collapseImpossible")

CLAY_HARD_CORE = "collapseImpossible"
CALC12_ROUTE_SELECTOR = {
    "calc": "Calc12",
    "route_selector": "statistical",
    "power_law": "|<omega,e2>|^2 ~ C*g12^beta",
    "beta_decision_thresholds": {
        ">1": "regularity_consistent",
        "<1": "blowup_precursor",
        "CI straddles 1": "inconclusive",
    },
    "proof_blocking": False,
    "no_further_calcs_blocking": True,
}


REQUIRED_KEYS = (
    "contract",
    "version",
    "control_card",
    "calc11_complete",
    "calc11_decision",
    "no_further_calcs_blocking",
    "closeable_packages",
    "closeable_package_count",
    "remaining_hard_walls",
    "hard_wall_count",
    "clay_hard_core",
    "optional_next_calc",
    "calc12_route_selector",
    "optional_next_calc_blocks_proof",
    "proof_blocking",
    "clay_promotion",
    "theorem_promotion",
    "parity_hash",
    "validation_passed",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_payload() -> dict[str, Any]:
    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "version": VERSION,
        "control_card": dict(CONTROL_CARD),
        "calc11_complete": True,
        "calc11_decision": "no_special_alignment",
        "no_further_calcs_blocking": True,
        "closeable_packages": list(CLOSEABLE_PACKAGES),
        "closeable_package_count": len(CLOSEABLE_PACKAGES),
        "remaining_hard_walls": list(REMNANT_HARD_WALLS),
        "hard_wall_count": len(REMNANT_HARD_WALLS),
        "clay_hard_core": CLAY_HARD_CORE,
        "optional_next_calc": CALC12_ROUTE_SELECTOR,
        "calc12_route_selector": CALC12_ROUTE_SELECTOR,
        "optional_next_calc_blocks_proof": False,
        "proof_blocking": False,
        "clay_promotion": False,
        "theorem_promotion": False,
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

    if not all(key in payload for key in REQUIRED_KEYS):
        return False

    if payload.get("contract") != CONTRACT:
        return False
    if payload.get("version") != VERSION:
        return False

    control_card = payload.get("control_card")
    if not isinstance(control_card, dict) or set(control_card) != set(CONTROL_CARD):
        return False
    if control_card != CONTROL_CARD:
        return False

    if payload.get("calc11_complete") is not True:
        return False
    if payload.get("calc11_decision") != "no_special_alignment":
        return False
    if payload.get("no_further_calcs_blocking") is not True:
        return False

    closeable_packages = payload.get("closeable_packages")
    if not isinstance(closeable_packages, list) or closeable_packages != list(CLOSEABLE_PACKAGES):
        return False
    if payload.get("closeable_package_count") != len(CLOSEABLE_PACKAGES):
        return False

    remaining_walls = payload.get("remaining_hard_walls")
    if not isinstance(remaining_walls, list) or remaining_walls != list(REMNANT_HARD_WALLS):
        return False
    if payload.get("hard_wall_count") != len(REMNANT_HARD_WALLS):
        return False
    if payload.get("clay_hard_core") != CLAY_HARD_CORE:
        return False
    if payload.get("optional_next_calc") != CALC12_ROUTE_SELECTOR:
        return False
    if payload.get("calc12_route_selector") != CALC12_ROUTE_SELECTOR:
        return False
    if payload.get("optional_next_calc_blocks_proof") is not False:
        return False
    if payload.get("proof_blocking") is not False:
        return False

    if payload.get("clay_promotion") is not False:
        return False
    if payload.get("theorem_promotion") is not False:
        return False

    parity_hash = payload.get("parity_hash")
    if not isinstance(parity_hash, str) or len(parity_hash) != 64:
        return False
    try:
        int(parity_hash, 16)
    except ValueError:
        return False

    expected = stable_hash(
        {k: v for k, v in payload.items() if k not in {"parity_hash", "validation_passed"}}
    )
    if parity_hash != expected:
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
