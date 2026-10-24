"""Synthetic Nobel optogenetic causal collision regressions. No neuro-data."""
from __future__ import annotations
from pathlib import Path
import importlib.util
import sys
import unittest

FILE=Path(__file__).resolve().parents[1]/"scripts"/"check_hardt_optogenetic_nobel_causal_cut.py"
SPEC=importlib.util.spec_from_file_location("hardt_nobel_optical",FILE)
assert SPEC is not None and SPEC.loader is not None
m=importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name]=m
SPEC.loader.exec_module(m)

class TestNobelOpticalCausality(unittest.TestCase):
    def test_full_factorial_neural_and_pickup_collision(self):
        result=m.collision_audit()
        self.assertTrue(result["positive_light_opsin_full_factorial_rows_identical_for_neural_and_opsin_correlated_artifact"])
        self.assertFalse(result["identified_network_transmission_from_unblocked_optics_alone"])

    def test_ordinary_heat_control(self):
        self.assertEqual(m.difference_in_differences(m.four_arm("ordinary_light_heating")),0)

    def test_opsin_neural_interaction(self):
        self.assertEqual(m.difference_in_differences(m.four_arm("opsin_neural")),1)

    def test_conditional_downstream_blocker(self):
        self.assertEqual(m.four_arm("opsin_neural",blocked=1)[1,1],0)
        self.assertEqual(m.four_arm("opsin_correlated_optical_artifact",blocked=1)[1,1],1)

    def test_343_additive_models(self):
        self.assertEqual(m.exhaustive_nulls()["additive_control_models_checked"],343)

    def test_independent_hidden_target(self):
        self.assertTrue(m.independent_channel_and_target_gate()["remote_person_target_address_not_inferred"])

    def test_2x2x2_opsin_vs_spin_triple_interaction(self):
        r=m.three_factor_spin_vs_opsin_discriminator()
        self.assertEqual(r["pure_opsin_magnetic_field_three_factor_interaction"],0)
        self.assertEqual(r["declared_spin_receptor_three_factor_interaction"],1)

    def test_2187_lower_order_nulls(self):
        self.assertEqual(
            m.three_factor_spin_vs_opsin_discriminator()["at_most_pairwise_exact_nulls_checked"],
            2187)

    def test_fail_closed_experimental_promotion(self):
        self.assertEqual(m.mechanism_manifest()["claim"]["claim_promotion"],"NOT_AUTHORIZED")

if __name__=="__main__":
    unittest.main()
