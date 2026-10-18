from __future__ import annotations

import json

RETRIEVED = "2026-09-16"

OEIS_42B_SEQUENCE = "A058676"
OEIS_42B_LABEL = "42b"
ATLAS_42B_LABEL = "42B"

POWER_MAP = {
    2: "21D",
    3: "14C",
    7: "6B",
    14: "3B",
    21: "2B",
}


def build_42b_power_bridge_receipt() -> dict[str, object]:
    return {
        "retrieved": RETRIEVED,
        "oeis_sequence": OEIS_42B_SEQUENCE,
        "oeis_label": OEIS_42B_LABEL,
        "atlas_label": ATLAS_42B_LABEL,
        "atlas_second_power_target": POWER_MAP[2],
        "atlas_third_power_target": POWER_MAP[3],
        "atlas_seventh_power_target": POWER_MAP[7],
        "atlas_fourteenth_power_target": POWER_MAP[14],
        "atlas_twenty_first_power_target": POWER_MAP[21],
        "direct_power_bridge_to_3B": POWER_MAP[14] == "3B",
        "same_class_paid": True,
        "creates_n3b_action_weld": False,
        "creates_monster_representation_theorem": False,
        "next_residual": (
            "Use 42B/42b, not 42D/42d, as the order-42 power-map route to 3B. "
            "The class-power identity localizes the correct conjugacy-class bridge but "
            "does not construct the selected N(3B) subgroup action or intertwiner."
        ),
    }


def main() -> int:
    print(json.dumps(build_42b_power_bridge_receipt(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
