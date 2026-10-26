"""Synthetic MATLAB EEGLAB metadata regressions; no original EEG arrays vendored."""
import tempfile
import unittest
from pathlib import Path
import numpy as np
from scipy.io import savemat
from scripts.audit_dmt_eeg_recording_epochs import metadata_audit


def source_fixture(folder, labels=None):
    labels = labels or [
        "1001_1 _ condition1_DMT", "1001_1 _ condition1_DMT",
        "X_harmine", "1001_2 _ condition1_harmine",
        "1001_3 _ condition1_placebo", "1001_3 _ condition1_placebo"]
    event = np.empty((1, len(labels)), dtype=[("eventtype", "O")])
    for i, x in enumerate(labels):
        event[0, i] = (x,)
    s = Path(folder) / "1001_equalised.set"
    savemat(s, {"EEG": {"setname": "1001_equalised.set",
                        "data": "1001_equalised.fdt",
                        "nbchan": 1, "pnts": 2, "trials": len(labels),
                        "srate": 128, "epoch": event}})
    f = Path(folder) / "1001_equalised.fdt"
    f.write_bytes(b"\0" * (1*2*len(labels)*4))
    return s, f


class EEGLABEventMetadataTests(unittest.TestCase):
    def test_boundary_counts_are_real_arm_epochs(self):
        with tempfile.TemporaryDirectory() as d:
            s, f = source_fixture(d)
            a = metadata_audit(s, f)
            self.assertEqual(a["original_arm_epoch_counts"],
                             {"DMT": 2, "harmine": 2, "placebo": 2})
            self.assertEqual(a["source_X_arm_only_boundary_marker_epochs"]["harmine"], 1)
            self.assertEqual(a["arm_epochs_with_explicit_visit_indices"]["harmine"], 1)
            self.assertTrue(a["all_original_epochs_accounted_for"])

    def test_source_visit_indices_and_nonpromotion(self):
        with tempfile.TemporaryDirectory() as d:
            s, f = source_fixture(d)
            a = metadata_audit(s, f)
            self.assertEqual(a["original_arm_visit_indices"],
                             {"DMT": 1, "harmine": 2, "placebo": 3})
            self.assertFalse(a["individual_X_epoch_visit_identity_verified"])
            self.assertFalse(a["original_microstate_G1_computed"])
            self.assertTrue(a["fdt_extent_matched"])

    def test_missing_fdt_is_only_a_coverage_gap(self):
        with tempfile.TemporaryDirectory() as d:
            s, f = source_fixture(d)
            f.unlink()
            self.assertFalse(metadata_audit(s)["fdt_extent_matched"])
            with self.assertRaises(ValueError):
                metadata_audit(s, f)

    def test_bad_fdt_extent_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            s, f = source_fixture(d)
            f.write_bytes(b"wrong")
            with self.assertRaises(ValueError):
                metadata_audit(s, f)

    def test_ambiguous_epoch_arm_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            labels = ["X_DMT", "X_harmine", "X_placebo",
                      "1001_1 _ condition1_DMT",
                      "1001_2 _ condition1_harmine",
                      "1001_3 _ condition1_DMT"]
            s, f = source_fixture(d, labels)
            with self.assertRaises(ValueError):
                metadata_audit(s, f)

    def test_one_arm_multiple_visits_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            labels = ["1001_1 _ condition1_DMT",
                      "1001_2 _ condition1_DMT",
                      "1001_3 _ condition1_harmine",
                      "1001_3 _ condition1_harmine",
                      "1001_2 _ condition1_placebo",
                      "1001_2 _ condition1_placebo"]
            s, f = source_fixture(d, labels)
            with self.assertRaises(ValueError):
                metadata_audit(s, f)

    def test_untyped_original_boundary_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            labels = ["1001_1 _ condition1_DMT", "X_DMT",
                      "X_harmine", "1001_2 _ condition1_harmine",
                      "1001_3 _ condition1_placebo", "X_UNKNOWN"]
            s, f = source_fixture(d, labels)
            with self.assertRaises(ValueError):
                metadata_audit(s, f)


if __name__ == "__main__":
    unittest.main()
