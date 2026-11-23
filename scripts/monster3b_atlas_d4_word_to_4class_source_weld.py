#!/usr/bin/env python3
"""Join ORIGINAL #1098 ATLAS source-word D4 / Suzuki 2B receipt with
ORIGINAL #1250 CTblLib exact 2.Suz.2 -> Monster 4-class fusion receipt.

This imports no matrix algorithm and no class-table calculator: those are
separate source owners. It checks their source-relative witness interfaces.
Receipt JSON is not independent authentication of producer execution.
"""
import argparse
import hashlib
import json
from pathlib import Path

WORD_SCHEMA = "monster3b-atlas-source-rotation-suzuki-2B-by-7-centraliser-v1"
FUSION_SCHEMA = "monster3b-atlas-source-Suz2B-to-Monster4-fusion-v1"
def require(condition, message):
    if not condition:
        raise ValueError(message)

def check(word, fusion):
    require(type(word) is dict and type(fusion) is dict, "two typed source receipts required")
    require(word.get("schema") == WORD_SCHEMA, "wrong #1098 ATLAS source-word schema")
    require(fusion.get("schema") == FUSION_SCHEMA, "wrong #1250 source-fusion schema")
    require(word.get("prior_repo_owner_PR") == 1098, "original ATLAS witness owner mismatch")
    for key in ("source_matrix_SHA256_manifest_verified",
                "source_rotation_square_is_negative_identity",
                "centralizing_seven_has_order_7",
                "centralizing_seven_exactly_commutes_with_r",
                "centralizing_seven_preserves_original_alternating_form",
                "alternate_order7_centralizer_witness_verified"):
        require(word.get(key) is True, "ATLAS source-word witness missing: " + key)
    require(word.get("source_rotation_projective_Suzuki_involution_class") == "2B",
            "original r must project to Suzuki involution class 2B")
    require(word.get("atlas_Suzuki_twoA_centralizer_order") == 3317760
            and word.get("atlas_Suzuki_twoB_centralizer_order") == 161280,
            "Suzuki source centralizer values changed")
    require(word.get("atlas_Suzuki_twoA_centralizer_divisible_by_7") is False
            and word.get("atlas_Suzuki_twoB_centralizer_divisible_by_7") is True,
            "order-seven centralizer class sieve inconsistent")
    require(word.get("actual_Monster_3B_diagonal_quotient_weld") is False
            and word.get("actual_Wzeta_Hom_intertwiner_paid") is False,
            "upstream word producer must not pretend to prove Monster action")
    rows = fusion.get("candidates")
    require(type(rows) is list and len(rows) == 1,
            "require exactly one original 2.Suz.2 order-four candidate class")
    require(fusion.get("source_two_suz_order4_candidates_count") == 1,
            "wrong source class count")
    require(fusion.get("status") == "UNIQUE_SOURCE_FUSION"
            and fusion.get("actual_monster_four_class_uniquely_forced_by_class_fusions") is True,
            "Monster 4-class not uniquely forced")
    row = rows[0]
    require(type(row) is dict and all(
        type(row.get(k)) is int and row[k] > 0
        for k in ("two_suz_class_position", "six_suz_class_position",
                  "main_class_position", "mn3b_class_position",
                  "monster_class_position")),
            "missing literal quotient class positions")
    require(row["two_suz_class_position"] == 5
            and row["monster_four_label"] == "4D"
            and fusion.get("all_possible_monster_four_labels") == ["4D"],
            "class-five / Monster-4D source selection failed")
    require(type(fusion.get("source_suz_2b_position")) is int
            and fusion["source_suz_2b_position"] > 0,
            "Suzuki source class coordinate missing")
    for key in ("literal_source_word_2Suz_class_individually_identified",
                "actual_6Suz_degree78_family_selected",
                "full_actual_Monster_Hom_constructed"):
        require(fusion.get(key) is False, "source-fusion producer overpromotes: " + key)
    return {
        "schema": "monster3b-atlas-actual-D4-word-to-Monster-4D-source-relative-weld-v1",
        "status": "SOURCE_RELATIVE_ACTUAL_WORD_CLASS_WELD_PASS",
        "original_ATLAS_source_owner_PR": 1098,
        "original_CTBLib_quotient_owner_PR": 1250,
        "source_word_rotation_SLP": word["source_rotation_word"],
        "source_word_suzuki_class": "2B",
        "selected_two_suz_class_position": row["two_suz_class_position"],
        "selected_six_suz_class_position": row["six_suz_class_position"],
        "selected_main_class_position": row["main_class_position"],
        "selected_mn3b_class_position": row["mn3b_class_position"],
        "selected_monster_class_position": row["monster_class_position"],
        "selected_monster_four_class": "4D",
        "conditional_monster_class_chain": ["4D", "12F", "6B"],
        "conditional_phase_trace": 66,
        "actual_source_word_to_two_suz_class_selected_under_ATLAS_and_CTBLib_alignment": True,
        "actual_Monster_generator_word_produced": False,
        "selected_diagonal_kernel_source_intertwiner_paid": False,
        "absolute_zeta3_orientation_paid": False,
        "actual_Monster_Hom_or_VOA_action_paid": False,
        "producer_execution_authenticated_by_this_consumer": False,
        "agda_kernel_checked_by_this_consumer": False
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("atlas_rotation_word_receipt", type=Path)
    parser.add_argument("monster_four_fusion_receipt", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    word_bytes = args.atlas_rotation_word_receipt.read_bytes()
    fusion_bytes = args.monster_four_fusion_receipt.read_bytes()
    result = check(json.loads(word_bytes), json.loads(fusion_bytes))
    result["provided_ATLAS_word_receipt_sha256"] = hashlib.sha256(word_bytes).hexdigest()
    result["provided_Monster_fusion_receipt_sha256"] = hashlib.sha256(fusion_bytes).hexdigest()
    encoded = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.out:
        args.out.write_text(encoded)
    print(encoded, end="")

if __name__ == "__main__":
    main()
