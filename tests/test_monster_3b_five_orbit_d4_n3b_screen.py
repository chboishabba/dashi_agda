from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "build" / "monster_3b_five_orbit_d4_n3b_screen.json"


def test_screen_receipt_separates_character_compatibility_from_actual_realization():
    assert FIXTURE.exists(), "run scripts/monster_3b_five_orbit_d4_n3b_screen.g first"
    receipt = json.loads(FIXTURE.read_text())

    assert receipt["target_character"] == [5, 5, 1, 3, 3]
    assert receipt["target_multiplicities"] == {
        "A1": 3,
        "A2": 0,
        "B1": 1,
        "B2": 1,
        "E": 0,
    }
    assert receipt["possible_fusion_count"] >= receipt["character_compatible_fusion_count"]
    assert receipt["character_compatible_fusion_count"] >= 0
    assert receipt["actual_d4_subgroup_realized"] in (True, False)
    assert receipt["selected_action_same_object_paid"] is False


def test_actual_realization_receipt_localizes_failure_stage():
    assert FIXTURE.exists(), "run scripts/monster_3b_five_orbit_d4_n3b_screen.g first"
    receipt = json.loads(FIXTURE.read_text())

    for key in (
        "atlas_group_realized",
        "d4_subgroup_found",
        "canonical_isomorphism_found",
        "ambient_class_fusion_unique",
        "actual_fusion_is_possible",
        "actual_character_compatible",
    ):
        assert receipt[key] in (True, False)

    if not receipt["atlas_group_realized"]:
        assert receipt["d4_subgroup_found"] is False
    if not receipt["d4_subgroup_found"]:
        assert receipt["canonical_isomorphism_found"] is False
    if not receipt["canonical_isomorphism_found"]:
        assert receipt["ambient_class_fusion_unique"] is False
    if not receipt["ambient_class_fusion_unique"]:
        assert receipt["actual_fusion_is_possible"] is False
    if not receipt["actual_fusion_is_possible"]:
        assert receipt["actual_character_compatible"] is False

    assert receipt["actual_d4_subgroup_realized"] == (
        receipt["d4_subgroup_found"]
        and receipt["canonical_isomorphism_found"]
        and receipt["ambient_class_fusion_unique"]
    )


def test_screen_never_promotes_possible_fusion_to_actual_subgroup():
    assert FIXTURE.exists(), "run scripts/monster_3b_five_orbit_d4_n3b_screen.g first"
    receipt = json.loads(FIXTURE.read_text())

    if not receipt["actual_d4_subgroup_realized"]:
        assert receipt["actual_realized_fusion"] is None
    assert receipt["possible_fusion_is_actual_subgroup"] is False
    assert receipt["character_match_creates_intertwiner"] is False
