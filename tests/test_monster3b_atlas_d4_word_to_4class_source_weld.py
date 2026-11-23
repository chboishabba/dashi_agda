#!/usr/bin/env python3
"""Synthetic fail-closed interface tests; never authenticate GAP or ATLAS."""
import copy
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from monster3b_atlas_d4_word_to_4class_source_weld import check

def word_fixture():
    return {
        "schema": "monster3b-atlas-source-rotation-suzuki-2B-by-7-centraliser-v1",
        "prior_repo_owner_PR": 1098,
        "source_matrix_SHA256_manifest_verified": True,
        "source_rotation_square_is_negative_identity": True,
        "centralizing_seven_has_order_7": True,
        "centralizing_seven_exactly_commutes_with_r": True,
        "centralizing_seven_preserves_original_alternating_form": True,
        "alternate_order7_centralizer_witness_verified": True,
        "source_rotation_projective_Suzuki_involution_class": "2B",
        "atlas_Suzuki_twoA_centralizer_order": 3317760,
        "atlas_Suzuki_twoB_centralizer_order": 161280,
        "atlas_Suzuki_twoA_centralizer_divisible_by_7": False,
        "atlas_Suzuki_twoB_centralizer_divisible_by_7": True,
        "actual_Monster_3B_diagonal_quotient_weld": False,
        "actual_Wzeta_Hom_intertwiner_paid": False,
        "source_rotation_word": "m*g*m*g^-1 (m=(W)^5)",
    }

def fusion_fixture():
    return {
        "schema": "monster3b-atlas-source-Suz2B-to-Monster4-fusion-v1",
        "candidates": [{
            "two_suz_class_position": 5,
            "two_suz_class_order": 4,
            "two_suz_centralizer_order": 322560,
            "two_suz_square_central_position": 2,
            "two_suz_outer_image_position": 4,
            "six_suz_class_position": 8,
            "main_class_position": 10,
            "mn3b_class_position": 12,
            "monster_class_position": 14,
            "monster_four_label": "4D",
        }],
        "source_two_suz_order4_candidates_count": 1,
        "status": "UNIQUE_SOURCE_FUSION",
        "actual_monster_four_class_uniquely_forced_by_class_fusions": True,
        "all_possible_monster_four_labels": ["4D"],
        "source_suz_2b_position": 3,
        "source_suz_outer_position": 4,
        "source_two_suz_central_minus_one_position": 2,
        "literal_source_word_2Suz_class_individually_identified": False,
        "actual_6Suz_degree78_family_selected": False,
        "full_actual_Monster_Hom_constructed": False,
    }

class SourceWeld(unittest.TestCase):
    def test_exact_source_relative_weld(self):
        result = check(word_fixture(), fusion_fixture())
        self.assertEqual(result["selected_monster_four_class"], "4D")
        self.assertEqual(result["conditional_phase_trace"], 66)
        self.assertEqual(result["selected_two_suz_class_position"], 5)
        self.assertFalse(result["actual_Monster_Hom_or_VOA_action_paid"])
        self.assertFalse(result["producer_execution_authenticated_by_this_consumer"])

    def test_missing_seven_centraliser(self):
        w=word_fixture();w["centralizing_seven_exactly_commutes_with_r"]=False
        with self.assertRaises(ValueError):check(w,fusion_fixture())

    def test_wrong_suzuki_class(self):
        w=word_fixture();w["source_rotation_projective_Suzuki_involution_class"]="2A"
        with self.assertRaises(ValueError):check(w,fusion_fixture())

    def test_wrong_centralizer_datum(self):
        w=word_fixture();w["atlas_Suzuki_twoA_centralizer_order"]=161280
        with self.assertRaises(ValueError):check(w,fusion_fixture())

    def test_ambiguous_fusion(self):
        f=fusion_fixture();f["status"]="AMBIGUOUS_SOURCE_FUSION"
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_wrong_double_cover_class(self):
        f=fusion_fixture();f["candidates"][0]["two_suz_class_position"]=6
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_wrong_monster_class(self):
        f=fusion_fixture();f["candidates"][0]["monster_four_label"]="4A"
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_two_candidates(self):
        f=fusion_fixture();f["candidates"].append(copy.deepcopy(f["candidates"][0]))
        f["source_two_suz_order4_candidates_count"]=2
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_falsely_promoted_action(self):
        f=fusion_fixture();f["full_actual_Monster_Hom_constructed"]=True
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_boolean_class_index(self):
        f=fusion_fixture();f["candidates"][0]["six_suz_class_position"]=True
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_wrong_actual_centralizer(self):
        f=fusion_fixture();f["candidates"][0]["two_suz_centralizer_order"]=2419200
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_misidentified_square(self):
        f=fusion_fixture();f["candidates"][0]["two_suz_square_central_position"]=3
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_misidentified_outer_quotient(self):
        f=fusion_fixture();f["candidates"][0]["two_suz_outer_image_position"]=5
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_missing_actual_class_order(self):
        f=fusion_fixture();del f["candidates"][0]["two_suz_class_order"]
        with self.assertRaises(ValueError):check(word_fixture(),f)

    def test_missing_source_manifest(self):
        w=word_fixture();w["source_matrix_SHA256_manifest_verified"]=False
        with self.assertRaises(ValueError):check(w,fusion_fixture())

if __name__=="__main__":
    unittest.main()
