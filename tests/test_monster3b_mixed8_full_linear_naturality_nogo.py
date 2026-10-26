#!/usr/bin/env python3
"""Focused finite naturality negative controls, no external Monster claims."""
import sys
import unittest
from pathlib import Path
from itertools import product

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_mixed8_full_linear_naturality_nogo as model


class FullLinearNaturalityNoGo(unittest.TestCase):
    def test_quaternion_commutator(self):
        self.assertEqual(model.mul(model.A,model.A),model.MINUS_I)
        self.assertEqual(model.mul(model.B,model.B),model.MINUS_I)
        self.assertEqual(model.commutator(model.A,model.B),model.MINUS_I)
        self.assertNotEqual(model.MINUS_I,model.I)

    def test_half_turn_on_source_and_target(self):
        for x in product(model.F,repeat=4):
            if any(x):
                self.assertEqual(model.rotate(model.rotate(x)),
                                 model.source_action(model.MINUS_I,x))
        for y in product(model.F,repeat=2):
            if any(y):
                self.assertNotEqual(model.rotate(model.rotate(y)),y)

    def test_all_group_and_target_checks(self):
        receipt=model.certificate()
        self.assertEqual(receipt["source_centralizer_order"],48)
        self.assertEqual(receipt["target_centralizer_order"],4)
        self.assertFalse(receipt["full_linear_natural_D4_map_exists"])
        self.assertFalse(receipt["balanced_fibres_required_for_no_go"])

    def test_no_source_or_kernel_promotion(self):
        receipt=model.certificate()
        for flag in ("selected_Monster_source_word","actual_6Suz_degree78_selected",
                     "Heisenberg_Hom_constructed","IIT_observable_identified",
                     "Agda_kernel_checked"):
            self.assertIs(receipt[flag],False)


if __name__=="__main__":
    unittest.main()
