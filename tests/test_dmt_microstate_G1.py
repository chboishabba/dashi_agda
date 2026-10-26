"""+microstate exact-count G1 synthetic regression (NOT human EEG reproduction)."""
import copy
import math
import unittest

from scripts.audit_dmt_microstate_G1 import (
    SCHEMA, ORIGINAL_TOOLBOX_BLOB, g1_counts, synthetic_evaluate)


def fixture(labels=None):
    if labels is None:
        labels = [1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 3, 1]
    return {"schema": SCHEMA, "mode": "synthetic",
            "source_id": "synthetic:author-G1-control", "labels": labels,
            "single_contiguous_stream": True}


class TestOriginalG1(unittest.TestCase):
    def test_nonzero_exact_log_two(self):
        result = g1_counts(fixture()["labels"])
        self.assertAlmostEqual(result["g1"], 4 * math.log(2), places=12)
        self.assertEqual(result["df_original_chi_square"], 12)

    def test_single_cycle_first_order_G1_zero(self):
        self.assertAlmostEqual(g1_counts([1, 2, 3, 1, 2, 3, 1, 2, 3])["g1"], 0, places=12)

    def test_alternating_sequence_is_order_one(self):
        self.assertEqual(g1_counts([1, 2, 1, 2, 1, 2, 1])["g1"], 0.0)

    def test_constant_single_state(self):
        res = g1_counts([1, 1, 1, 1])
        self.assertEqual(res["g1"], 0.0)
        self.assertEqual(res["df_original_chi_square"], 0)

    def test_label_permutation_invariance(self):
        labels = fixture()["labels"]
        relabel = {1: 3, 2: 1, 3: 2}
        self.assertAlmostEqual(g1_counts(labels)["g1"],
                               g1_counts([relabel[x] for x in labels])["g1"], 12)

    def test_reversal_conditional_information(self):
        # This identity holds for mutual conditional information under reversal.
        labels = fixture()["labels"]
        self.assertAlmostEqual(g1_counts(labels)["g1"],
                               g1_counts(list(reversed(labels)))["g1"], 12)

    def test_no_raw_source_mode(self):
        f = fixture(); f["mode"] = "authorized_research"
        with self.assertRaises(ValueError):
            synthetic_evaluate(f)

    def test_no_raw_eeg_extra_field(self):
        f = fixture(); f["raw_eeg_bytes"] = "not a valid field"
        with self.assertRaises(ValueError):
            synthetic_evaluate(f)

    def test_no_real_study_source_alias(self):
        f = fixture(); f["source_id"] = "zenodo:18850897"
        with self.assertRaises(ValueError):
            synthetic_evaluate(f)

    def test_no_unverified_epoch_boundaries(self):
        f = fixture(); f["single_contiguous_stream"] = False
        with self.assertRaises(ValueError):
            synthetic_evaluate(f)

    def test_missing_labels_compacted_as_original_MATLAB(self):
        sparse = g1_counts([1, 3, 1, 3, 3])
        dense = g1_counts([1, 2, 1, 2, 2])
        self.assertAlmostEqual(sparse["g1"], dense["g1"], places=12)
        self.assertEqual(sparse["k_observed"], 2)
        self.assertEqual(sparse["original_state_support"], [1, 3])
        self.assertTrue(sparse["unobserved_state_indices_compacted"])
        self.assertFalse(dense["unobserved_state_indices_compacted"])

    def test_bool_label_rejected(self):
        with self.assertRaises(ValueError):
            g1_counts([1, True, 1])

    def test_empty_short_rejected(self):
        for seq in [[], [1], [1, 2]]:
            with self.assertRaises(ValueError):
                g1_counts(seq)

    def test_source_provenance_ceiling(self):
        res = synthetic_evaluate(fixture())
        self.assertEqual(res["original_toolbox_git_blob"], ORIGINAL_TOOLBOX_BLOB)
        self.assertFalse(res["actual_eeg_participant_data_replayed"])
        self.assertFalse(res["original_p_value_reproduced"])
        self.assertFalse(res["independent_external_agents_inferred"])
        self.assertEqual(res["triples"], 10)


if __name__ == "__main__":
    unittest.main()
