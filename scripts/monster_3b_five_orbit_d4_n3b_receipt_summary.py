from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


REQUIRED_BOOL_KEYS = (
    "atlas_group_realized",
    "d4_subgroup_found",
    "canonical_isomorphism_found",
    "ambient_class_fusion_unique",
    "actual_fusion_is_possible",
    "actual_character_compatible",
)


def _require_receipt_shape(receipt: dict[str, Any]) -> None:
    for key in ("possible_fusion_count", "character_compatible_fusion_count"):
        value = receipt.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError(f"{key} must be a nonnegative integer")

    if receipt["character_compatible_fusion_count"] > receipt["possible_fusion_count"]:
        raise ValueError("character-compatible fusion count exceeds possible fusion count")

    for key in REQUIRED_BOOL_KEYS:
        if receipt.get(key) not in (True, False):
            raise ValueError(f"{key} must be boolean")

    if receipt.get("selected_action_same_object_paid") is not False:
        raise ValueError("runtime receipt must not pay selected-action same-object authority")
    if receipt.get("character_match_creates_intertwiner") is not False:
        raise ValueError("character match must not create an intertwiner")

    if not receipt["atlas_group_realized"] and receipt["d4_subgroup_found"]:
        raise ValueError("D4 subgroup cannot be found when Atlas group realization failed")
    if not receipt["d4_subgroup_found"] and receipt["canonical_isomorphism_found"]:
        raise ValueError("canonical isomorphism cannot be found before the D4 subgroup")
    if not receipt["canonical_isomorphism_found"] and receipt["ambient_class_fusion_unique"]:
        raise ValueError("ambient fusion cannot be unique before the canonical isomorphism")
    if not receipt["ambient_class_fusion_unique"] and receipt["actual_fusion_is_possible"]:
        raise ValueError("actual fusion cannot be admitted while ambient fusion is ambiguous")
    if not receipt["actual_fusion_is_possible"] and receipt["actual_character_compatible"]:
        raise ValueError("actual character compatibility requires an admitted actual fusion")


def classify_receipt(receipt: dict[str, Any]) -> str:
    """Return the first unresolved/falsifying seam in the execution ladder."""
    _require_receipt_shape(receipt)

    if receipt["character_compatible_fusion_count"] == 0:
        return "no-compatible-table-fusion"
    if not receipt["atlas_group_realized"]:
        return "atlas-group-realization-residual"
    if not receipt["d4_subgroup_found"]:
        return "d4-subgroup-realization-residual"
    if not receipt["canonical_isomorphism_found"]:
        return "canonical-d4-isomorphism-residual"
    if not receipt["ambient_class_fusion_unique"]:
        return "ambient-class-fusion-residual"
    if not receipt["actual_fusion_is_possible"]:
        return "actual-fusion-admissibility-residual"
    if not receipt["actual_character_compatible"]:
        return "actual-d4-wrong-embedding"
    return "selected-carrier-intertwiner-weld"


def summarize_receipt(receipt: dict[str, Any]) -> dict[str, Any]:
    stage = classify_receipt(receipt)
    return {
        "stage": stage,
        "possible_fusion_count": receipt["possible_fusion_count"],
        "character_compatible_fusion_count": receipt["character_compatible_fusion_count"],
        "atlas_group_realized": receipt["atlas_group_realized"],
        "d4_subgroup_found": receipt["d4_subgroup_found"],
        "canonical_isomorphism_found": receipt["canonical_isomorphism_found"],
        "ambient_class_fusion_unique": receipt["ambient_class_fusion_unique"],
        "actual_fusion_is_possible": receipt["actual_fusion_is_possible"],
        "actual_character_compatible": receipt["actual_character_compatible"],
        "five_orbit_route_falsified": stage == "no-compatible-table-fusion",
        "selected_action_same_object_paid": False,
        "selected_action_intertwiner_paid": False,
        "runtime_screen_creates_monster_theorem": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Classify the five-orbit D4/N(3B) runtime receipt")
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    receipt = json.loads(args.receipt.read_text())
    summary = summarize_receipt(receipt)
    text = json.dumps(summary, indent=2, sort_keys=True) + "\n"

    if args.output is None:
        print(text, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
