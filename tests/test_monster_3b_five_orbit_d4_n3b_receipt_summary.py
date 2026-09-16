from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SUMMARY = ROOT / "scripts" / "monster_3b_five_orbit_d4_n3b_receipt_summary.py"


def load_summary_module():
    assert SUMMARY.exists(), "expected D4/N3B receipt summary classifier"
    spec = importlib.util.spec_from_file_location("monster3b_d4_n3b_summary", SUMMARY)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def base_receipt() -> dict[str, object]:
    return {
        "possible_fusion_count": 1,
        "character_compatible_fusion_count": 1,
        "atlas_group_realized": True,
        "d4_subgroup_found": True,
        "canonical_isomorphism_found": True,
        "ambient_class_fusion_unique": True,
        "actual_fusion_is_possible": True,
        "actual_character_compatible": True,
        "selected_action_same_object_paid": False,
        "character_match_creates_intertwiner": False,
    }


def test_no_table_fusion_falsifies_five_orbit_route():
    m = load_summary_module()
    r = base_receipt()
    r["possible_fusion_count"] = 0
    r["character_compatible_fusion_count"] = 0
    assert m.classify_receipt(r) == "no-compatible-table-fusion"


def test_structural_fusions_without_character_match_also_falsify_route():
    m = load_summary_module()
    r = base_receipt()
    r["possible_fusion_count"] = 3
    r["character_compatible_fusion_count"] = 0
    assert m.classify_receipt(r) == "no-compatible-table-fusion"


def test_no_actual_group_localizes_atlas_realization_residual():
    m = load_summary_module()
    r = base_receipt()
    r.update({
        "atlas_group_realized": False,
        "d4_subgroup_found": False,
        "canonical_isomorphism_found": False,
        "ambient_class_fusion_unique": False,
        "actual_fusion_is_possible": False,
        "actual_character_compatible": False,
    })
    assert m.classify_receipt(r) == "atlas-group-realization-residual"


def test_missing_d4_localizes_subgroup_residual():
    m = load_summary_module()
    r = base_receipt()
    r.update({
        "d4_subgroup_found": False,
        "canonical_isomorphism_found": False,
        "ambient_class_fusion_unique": False,
        "actual_fusion_is_possible": False,
        "actual_character_compatible": False,
    })
    assert m.classify_receipt(r) == "d4-subgroup-realization-residual"


def test_ambiguous_fusion_localizes_class_identification_residual():
    m = load_summary_module()
    r = base_receipt()
    r.update({
        "canonical_isomorphism_found": True,
        "ambient_class_fusion_unique": False,
        "actual_fusion_is_possible": False,
        "actual_character_compatible": False,
    })
    assert m.classify_receipt(r) == "ambient-class-fusion-residual"


def test_actual_incompatible_d4_localizes_wrong_embedding():
    m = load_summary_module()
    r = base_receipt()
    r["actual_character_compatible"] = False
    assert m.classify_receipt(r) == "actual-d4-wrong-embedding"


def test_actual_compatible_d4_stops_at_selected_action_weld():
    m = load_summary_module()
    r = base_receipt()
    assert m.classify_receipt(r) == "selected-carrier-intertwiner-weld"
    summary = m.summarize_receipt(r)
    assert summary["selected_action_same_object_paid"] is False
    assert summary["selected_action_intertwiner_paid"] is False
