#!/usr/bin/env python3
"""Emit a compact audit of the post-Calc-11 closeable package surface."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


CONTRACT = "ns_clay_closeable_package_audit"
VERSION = 1
DEFAULT_OUTPUT = Path("outputs") / f"{CONTRACT}.json"

CLOSEABLE_PACKAGES: tuple[tuple[str, str], ...] = (
    ("millerToH5", "DASHI/Physics/Closure/NSKatoHessianConfinementReceipt.agda"),
    ("GD3 two-gap", "DASHI/Physics/Closure/NSKatoHessianConfinementReceipt.agda"),
    ("coareaGradientBound", "DASHI/Physics/Closure/NSCoareaGradientStepAPerComponentReceipt.agda"),
    ("LocalConcentration", "DASHI/Physics/Closure/LocalConcentrationPigeonConcentrationReceipt.agda"),
    ("pigeon_concentration", "DASHI/Physics/Closure/LocalConcentrationPigeonConcentrationReceipt.agda"),
    ("StepA_PerComponent", "DASHI/Physics/Closure/NSCoareaGradientStepAPerComponentReceipt.agda"),
    ("BoundaryHB_Correct", "DASHI/Physics/Closure/Lambda2PlusTransportInequalityBoundaryHBReceipt.agda"),
)

HARD_WALLS: tuple[str, ...] = ("KornLevelSet", "collapseImpossible")
HARD_WALL_RECEIPT_REF = "DASHI/Physics/Closure/NSHardTheoremKornCollapseWallPostCalc11Receipt.agda"
CLAY_HARD_CORE = "collapseImpossible"

CONTROL_CARD = {
    "O": "Worker 6 owns the post-Calc-11 closeable-package audit surface.",
    "R": (
        "Record the seven closeable package names, their target receipt refs, the two hard walls,"
        " and fail-closed promotion flags in one deterministic JSON ledger."
    ),
    "C": "A stdlib Python CLI only stats canonical Agda receipt files and emits compact JSON.",
    "S": "This is a status/control surface, not another route selector and not a theorem prover.",
    "L": (
        "package names -> target receipt refs -> hard walls -> clay hard core"
        " -> fail-closed promotion flags -> validation"
    ),
    "P": "Keep the package list exact, keep promotion false, and treat any missing receipt path as a failure.",
    "G": "Validation passes only when the seven closeable packages, the two hard walls, and the fail-closed flags all match the canonical surface.",
    "F": "No theorem promotion or Clay promotion is encoded; the surface fails closed if any receipt path is missing.",
}


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def receipt_exists(root: Path, receipt_ref: str) -> bool:
    return (root / receipt_ref).is_file()


def build_payload(root: Path | None = None) -> dict[str, Any]:
    root = repo_root() if root is None else root
    packages = [
        {
            "package_name": package_name,
            "target_receipt_ref": receipt_ref,
            "target_receipt_exists": receipt_exists(root, receipt_ref),
        }
        for package_name, receipt_ref in CLOSEABLE_PACKAGES
    ]

    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "version": VERSION,
        "control_card": dict(CONTROL_CARD),
        "closeable_packages": packages,
        "closeable_package_names": [item["package_name"] for item in packages],
        "closeable_package_count": len(packages),
        "hard_walls": list(HARD_WALLS),
        "hard_wall_count": len(HARD_WALLS),
        "hard_wall_receipt_ref": HARD_WALL_RECEIPT_REF,
        "hard_wall_receipt_exists": receipt_exists(root, HARD_WALL_RECEIPT_REF),
        "clay_hard_core": CLAY_HARD_CORE,
        "promotion": False,
        "promotion_flags": {
            "promotion_allowed": False,
            "promotion_blocked": True,
            "theorem_promotion": False,
            "clay_promotion": False,
        },
        "theorem_promotion": False,
        "clay_promotion": False,
        "validation_passed": False,
    }
    payload["validation_passed"] = validate_payload(payload, root=root)
    return payload


def validate_payload(payload: Any, *, root: Path | None = None) -> bool:
    if not isinstance(payload, dict):
        return False

    root = repo_root() if root is None else root
    if payload.get("contract") != CONTRACT or payload.get("version") != VERSION:
        return False

    control_card = payload.get("control_card")
    if not isinstance(control_card, dict) or set(control_card) != set(CONTROL_CARD):
        return False
    if control_card != CONTROL_CARD:
        return False

    packages = payload.get("closeable_packages")
    if not isinstance(packages, list) or len(packages) != len(CLOSEABLE_PACKAGES):
        return False
    if payload.get("closeable_package_count") != len(CLOSEABLE_PACKAGES):
        return False
    if payload.get("closeable_package_names") != [name for name, _ in CLOSEABLE_PACKAGES]:
        return False

    for package, (expected_name, expected_ref) in zip(packages, CLOSEABLE_PACKAGES, strict=True):
        if not isinstance(package, dict):
            return False
        if package.get("package_name") != expected_name:
            return False
        if package.get("target_receipt_ref") != expected_ref:
            return False
        if package.get("target_receipt_exists") is not True:
            return False
        if not receipt_exists(root, expected_ref):
            return False

    if payload.get("hard_walls") != list(HARD_WALLS):
        return False
    if payload.get("hard_wall_count") != len(HARD_WALLS):
        return False
    if payload.get("hard_wall_receipt_ref") != HARD_WALL_RECEIPT_REF:
        return False
    if payload.get("hard_wall_receipt_exists") is not True:
        return False
    if not receipt_exists(root, HARD_WALL_RECEIPT_REF):
        return False
    if payload.get("clay_hard_core") != CLAY_HARD_CORE:
        return False

    if payload.get("promotion") is not False:
        return False
    if payload.get("theorem_promotion") is not False:
        return False
    if payload.get("clay_promotion") is not False:
        return False

    flags = payload.get("promotion_flags")
    if not isinstance(flags, dict):
        return False
    expected_flags = {
        "promotion_allowed": False,
        "promotion_blocked": True,
        "theorem_promotion": False,
        "clay_promotion": False,
    }
    if flags != expected_flags:
        return False

    return True


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = build_payload()
    if not validate_payload(payload):
        print("ns_clay_closeable_package_audit: FAIL", file=sys.stderr)
        write_json(args.output, payload)
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 1

    write_json(args.output, payload)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
