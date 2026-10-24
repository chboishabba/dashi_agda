"""Regression tests for synthetic Hardt delta/OPM motion max-cut.
No human dataset or physical effect is asserted.
"""
from pathlib import Path
import importlib.util
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/"scripts"/"check_hardt_delta_opm_motion_maxcut.py"
SPEC=importlib.util.spec_from_file_location("hardt_delta_opm_motion",SOURCE)
assert SPEC is not None and SPEC.loader is not None
m=importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name]=m
SPEC.loader.exec_module(m)


class TestDeltaOPM(unittest.TestCase):
    def test_rank_recovery(self):
        x=m.source_vs_artifact()
        self.assertEqual(x["finite_rank_checks"],2028)
        self.assertTrue(x["brain_blind_reference_identifies_brain"])
        self.assertFalse(x["identical_sensitivity_reference_identifies_brain"])

    def test_motion_intervention_reversal(self):
        x=m.motion_lock_negative_control()
        self.assertEqual(x["confounded_train_fit_accuracy"],1.0)
        self.assertEqual(x["motion_reversed_test_fit_accuracy"],0.0)
        self.assertTrue(x["clean_reference_recovers_test_source"])

    def test_stimulus_common_cause(self):
        x=m.common_stimulus_negative_control()
        self.assertTrue(x["their_traces_are_perfectly_matched"])
        self.assertFalse(x["direct_receiver_to_receiver_coupling_in_model"])

    def test_missing_manifest_fails(self):
        x=m.validate_receipt({})
        self.assertFalse(x["admissible_for_experimental_review"])
        self.assertEqual(len(x["missing_receipts"]),15)

    def test_wrong_band_and_modality_fails(self):
        x={k:"dummy" for k in m.REQUIRED_RECEIPTS}
        x.update(recording_modality="human-EEG+OPM-MEG",
                 sampling_hz="1000",measured_delta_0p5_4Hz_noise_spectrum="40-Hz-SNR")
        res=m.validate_receipt(x)
        self.assertFalse(res["admissible_for_experimental_review"])
        self.assertIn("not a measured delta-band sensor noise spectrum",res["hard_errors"])

    def test_nonfinite_sampling_fails_preflight(self):
        for sample in ("NaN", "Infinity", "-Infinity", True):
            candidate={k:"dummy" for k in m.REQUIRED_RECEIPTS}
            candidate.update(recording_modality="human-OPM-MEG",
                             sampling_hz=sample)
            result=m.validate_receipt(candidate)
            self.assertFalse(result["admissible_for_experimental_review"])
            self.assertTrue(any("sampling_hz" in error for error in result["hard_errors"]))

    def test_full_synthetic_manifest_is_not_empirical_evidence(self):
        x={k:"synthetic-placeholder" for k in m.REQUIRED_RECEIPTS}
        x.update(recording_modality="human-OPM-MEG",sampling_hz=128)
        res=m.validate_receipt(x)
        self.assertFalse(res["admissible_for_experimental_review"])
        self.assertIn("does not establish causal",res["note"])
        self.assertIn("placeholder values cannot be promoted as experimental receipts",res["hard_errors"])


if __name__=="__main__":
    unittest.main()
