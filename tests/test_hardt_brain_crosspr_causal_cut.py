"""Finite tests for Hardt/BRAIN cross-PR causal discriminator.
Only synthetic fixtures; no EEG/MEG/fMRI observation or physical claim.
"""
from __future__ import annotations
from pathlib import Path
import importlib.util
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
PATH=ROOT/"scripts"/"check_hardt_brain_crosspr_causal_cut.py"
SPEC=importlib.util.spec_from_file_location("hardt_brain_crosspr",PATH)
assert SPEC is not None and SPEC.loader is not None
MOD=importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name]=MOD
SPEC.loader.exec_module(MOD)


class TestHardtBrainConsumerCut(unittest.TestCase):
    def test_finite_observational_do_collision(self):
        result=MOD.causal_collision()
        self.assertEqual(result["worlds"],16)
        self.assertEqual(result["passive_observation_fibres"],4)
        self.assertEqual(result["intervention_ambiguous_fibres"],4)
        self.assertTrue(result["no_closed_coarse_intervention_transition"])

    def test_viewed_not_independent_hidden_target(self):
        result=MOD.concealed_target_collision()
        self.assertTrue(result["viewed_image_consumer_retained"])
        self.assertTrue(result["independent_secret_not_recoverable"])
        self.assertTrue(result["leaked_secret_decodable"])

    def test_cross_modal_wrong_type(self):
        result=MOD.modality_receipt_fail_closed()
        self.assertEqual(result["wrong_type_mappings_rejected"],6)

    def test_original_dashiBRAIN_is_optional(self):
        result=MOD.optional_brain_runtime(None)
        self.assertEqual(result["status"],"NOT_IMPORTED")

    def test_unpinned_original_runtime_fails_before_code_execution(self):
        with self.assertRaisesRegex(ValueError,"blob mismatch"):
            MOD.optional_brain_runtime(__file__)


if __name__=="__main__":
    unittest.main()
