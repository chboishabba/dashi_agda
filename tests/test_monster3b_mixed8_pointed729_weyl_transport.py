#!/usr/bin/env python3
"""Verify transported finite Weyl relations; reject Monster source promotion."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_mixed8_pointed729_weyl_transport as model


class TransportedWeyl(unittest.TestCase):
    def test_selected_generator_relation(self):
        p=model.TO_ADDR[(model.E[0],model.E[0],model.E[0])]
        for i,v in enumerate(model.UNIT):
            self.assertEqual(model.dot(v,v),1)
            self.assertEqual(model.modulated_phase(model.translated(p,v),v),1)

    def test_complete_finite_certificate(self):
        receipt=model.verify()
        self.assertEqual(receipt["weyl_generator_pair_checks"],26244)
        self.assertEqual(receipt["D4_model_covariant_generator_checks"],8748)
        self.assertEqual(receipt["central_nine_projector_preserving_translations"],9)
        self.assertEqual(receipt["central_nine_projector_moving_translations"],720)
        self.assertFalse(receipt["same_source_normalizer_lift_established"])
        self.assertFalse(receipt["actual_Monster_Hom_constructed"])
        self.assertFalse(receipt["Agda_kernel_verified"])


if __name__=="__main__":
    unittest.main()
