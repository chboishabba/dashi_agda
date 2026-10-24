#!/usr/bin/env python3
"""Regression: source-conditional original JFine pointed-bulk Monster no-go.

Does not require GAP. Does not assert that the source-class inputs have been
revalidated against a live GAP table; original ATLAS/BW are prior sources.
"""
import importlib.util
from pathlib import Path
import unittest

HERE=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location(
    "jfine_d4_nogo",HERE/"scripts/jfine_3b_oriented_h4_d4_residual_nogo.py")
m=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(m)

class MonsterD4ResidualTest(unittest.TestCase):
    def test_multiplicity_obstruction(self):
        a=m.audit()
        self.assertEqual(a['negative_trivial_multiplicity'],-19)
        self.assertFalse(a['direct_product_bulk_plus_53_split_possible'])
        self.assertTrue(a['C4_phase_trace_compatibility_remains_true'])
    def test_both_reflections_must_be_2B(self):
        a=m.audit()
        self.assertEqual(a['forced_inverting_reflection_Monster_class'],'2B')
        self.assertEqual(a['unique_admissible_marker_involution_trace'],4)
    def test_source_character_and_positive_bulk(self):
        a=m.audit()
        self.assertEqual(a['pointed_bulk_character']['quarter'],54)
        self.assertEqual(a['full_irreducible_multiplicities']['A1'],25307)
        self.assertEqual(a['bulk_irreducible_multiplicities']['A1'],25326)
        self.assertEqual(a['residual_irreducible_multiplicities']['E'],14)
    def test_not_universal_no_go(self):
        a=m.audit()
        self.assertFalse(a['all_possible_nonproduct_Monster_actions_ruled_out'])
        self.assertFalse(a['actual_Monster_action_or_group_words_observed'])

if __name__=="__main__":unittest.main()
