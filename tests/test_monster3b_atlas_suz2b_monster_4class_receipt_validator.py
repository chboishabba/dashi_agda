#!/usr/bin/env python3
"""Synthetic fixtures verify only *receipt validation*, not GAP provenance."""
import importlib.util
import copy
import sys
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from monster3b_atlas_suz2b_monster_4class_receipt_validator import validate

def fixture(labels):
    rows=[dict(two_suz_class_position=i+4,
      six_suz_class_position=i+25,main_class_position=i+70,
      mn3b_class_position=i+20,monster_class_position=i+9,
      monster_four_label=cls) for i,cls in enumerate(labels)]
    unique=len(set(labels))==1
    return {
      "schema":"monster3b-atlas-source-Suz2B-to-Monster4-fusion-v1",
      "source_suz_2b_position":3,
      "source_suz_outer_position":5,
      "source_two_suz_central_minus_one_position":2,
      "actual_monster_twoB_position":3,
      "source_two_suz_order4_candidates_count":len(rows),
      "candidates":rows,
      "all_possible_monster_four_labels":sorted(set(labels)),
      "literal_source_word_2Suz_class_individually_identified":False,
      "actual_6Suz_degree78_family_selected":False,
      "full_actual_Monster_Hom_constructed":False,
      "actual_monster_four_class_uniquely_forced_by_class_fusions":unique,
      "status":"UNIQUE_SOURCE_FUSION" if unique else "AMBIGUOUS_SOURCE_FUSION"
    }

class SourceMonsterClassGateTest(unittest.TestCase):
    def test_unique_four_d_forces_six_b_branch_only(self):
        o=validate(fixture(["4D"]))
        assert o["selected_monster_four_class"]=="4D"
        assert len(o["conditional_class_phase_branches"]["4D"])==1
        assert o["conditional_class_phase_branches"]["4D"][0]["source_z_times_halfturn_class"]=="6B"
        assert o["conditional_class_phase_branches"]["4D"][0]["predicted_selected_phase_trace"]==66
    def test_unique_four_a_or_c(self):
        for cls,n in (("4A",1),("4C",2)):
            o=validate(fixture([cls]))
            assert o["selected_monster_four_class"]==cls
            assert len(o["conditional_class_phase_branches"][cls])==n
            assert all(x["predicted_selected_phase_trace"]==90
                       for x in o["conditional_class_phase_branches"][cls])
    def test_ambiguity_fails_closed(self):
        o=validate(fixture(["4A","4D","4C"]))
        assert o["selected_monster_four_class"] is None
        assert len(o["conditional_class_phase_branches"])==3
        assert not o["source_gap_execution_authenticated_by_python"]
    def test_invalid_class_rejected(self):
        p=fixture(["4A"]);p["candidates"][0]["monster_four_label"]="4B"
        with self.assertRaises(ValueError):validate(p)
    def test_fake_unique_rejected(self):
        p=fixture(["4A","4D"])
        p["actual_monster_four_class_uniquely_forced_by_class_fusions"]=True
        with self.assertRaises(ValueError):validate(p)
    def test_missing_label_rejected(self):
        p=fixture(["4A","4D"]);p["all_possible_monster_four_labels"]=["4A"]
        with self.assertRaises(ValueError):validate(p)
    def test_not_promoting_authenticity(self):
        for key in ("literal_source_word_2Suz_class_individually_identified",
                    "actual_6Suz_degree78_family_selected",
                    "full_actual_Monster_Hom_constructed"):
            p=fixture(["4C"]);p[key]=True
            with self.assertRaises(ValueError):validate(p)
    def test_duplicate_source_class_rejected(self):
        p=fixture(["4C","4C"])
        p["candidates"][1]["two_suz_class_position"]=p["candidates"][0]["two_suz_class_position"]
        with self.assertRaises(ValueError):validate(p)
    def test_invalid_index_and_bool_rejected(self):
        p=fixture(["4A"]);p["candidates"][0]["monster_class_position"]=True
        with self.assertRaises(ValueError):validate(p)
        p=fixture(["4A"]);p["actual_monster_twoB_position"]=0
        with self.assertRaises(ValueError):validate(p)

if __name__=="__main__":unittest.main()
