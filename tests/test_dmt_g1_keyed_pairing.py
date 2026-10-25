"""Synthetic acceptance/regression for source-keyed G1 comparison.

No original human EEG, G1 exports, rights receipts or patient identities used.
"""
from __future__ import annotations

import copy
import unittest
from fractions import Fraction

from scripts.audit_dmt_g1_keyed_pairing import (
    SCHEMA, ARMS, AUTHOR_CODE_COMMIT, AUTHOR_G1_EXPORT_SHA,
    TOOLBOX_G1_SHA, ZENODO_VERSION, AUTHOR_IDS,
    RECEIPT_SCHEMA, audit, canonical_sha256, validate)


def fixture():
    rows = []
    for pid, dmt, harmine, placebo in (
        ("s1", "10", "9", "8"),
        ("s2", "20", "19", "18"),
        ("s3", "30", "29", "28")):
        for arm, g1 in (("DMT", dmt), ("harmine", harmine),
                        ("placebo", placebo)):
            rows.append({"participant_id": pid, "arm": arm, "g1": g1,
                         "sample_count": 12,
                         "condition_session_reference": "synthetic-session-"+pid+"-"+arm,
                         "g1_label_stream_reference": "synthetic-G1-"+pid+"-"+arm,
                         "epoch_boundary_reference": "synthetic-single-epoch-"+pid+"-"+arm,
                         "label_sequence_type": "samplewise"})
    return {"schema": SCHEMA, "mode": "synthetic", "dataset_id": "synthetic:3-person-crossover",
            "analysis_source_commit": AUTHOR_CODE_COMMIT,
            "source_g1_export_blob": AUTHOR_G1_EXPORT_SHA,
            "source_toolbox_g1_blob": TOOLBOX_G1_SHA,
            "source_version_doi": ZENODO_VERSION,
            "condition_selection_provenance": "synthetic explicit condition-to-session map",
            "participant_crosswalk_provenance": "synthetic exact 3-ID roster",
            "recording_length_provenance": "synthetic 12-state ordered stream",
            "rows": rows}


class G1KeyedPairingTests(unittest.TestCase):
    def assert_invalid(self, doc, receipt=None):
        with self.assertRaises(ValueError):
            validate(doc, receipt)

    def test_synthetic_exact_contrasts(self):
        result = audit(fixture())
        self.assertEqual(result["participants"], 3)
        self.assertEqual(result["contrasts"]["DMT_vs_harmine"]["G1_raw"]["mean_exact"], "1")
        self.assertEqual(result["contrasts"]["DMT_vs_placebo"]["G1_raw"]["mean_exact"], "2")
        self.assertEqual(result["contrasts"]["DMT_vs_placebo"]["G1_raw"]["sample_variance_exact"], "0")
        self.assertEqual(result["contrasts"]["DMT_vs_placebo"]["conditional_information_per_triple_nats"]["mean_exact"], "1/10")
        self.assertFalse(result["original_experiment_reproduced"])

    def test_order_permutation_with_keys_invariant(self):
        f = fixture()
        result = audit(f)["contrasts"]
        f["rows"].reverse()
        self.assertEqual(audit(f)["contrasts"], result)

    def test_unkeyed_equal_length_export_not_a_pairing(self):
        f = fixture()
        f["rows"] = [{"arm": arm, "g1_values": ["10", "20", "30"]}
                     for arm in ARMS]
        self.assert_invalid(f)

    def test_same_marginals_different_paired_variance(self):
        f = fixture()
        baseline = audit(f)["contrasts"]["DMT_vs_placebo"]["G1_raw"]
        placebo = [row for row in f["rows"] if row["arm"] == "placebo"]
        permuted = [x["g1"] for x in placebo][::-1]
        for row, replacement in zip(placebo, permuted):
            row["g1"] = replacement
        shifted = audit(f)["contrasts"]["DMT_vs_placebo"]["G1_raw"]
        self.assertEqual(baseline["mean_exact"], shifted["mean_exact"])
        self.assertNotEqual(baseline["sample_variance_exact"], shifted["sample_variance_exact"])

    def test_missing_arm_rejected(self):
        f = fixture()
        f["rows"] = [r for r in f["rows"] if not (
            r["participant_id"] == "s2" and r["arm"] == "placebo")]
        self.assert_invalid(f)

    def test_duplicate_person_arm_rejected(self):
        f = fixture(); f["rows"].append(copy.deepcopy(f["rows"][0]))
        self.assert_invalid(f)

    def test_unknown_condition_rejected(self):
        f = fixture(); f["rows"][0]["arm"] = "ketamine"
        self.assert_invalid(f)

    def test_invalid_negative_G1_rejected(self):
        f = fixture(); f["rows"][0]["g1"] = "-0.5"
        self.assert_invalid(f)

    def test_nonstring_G1_rejected(self):
        f = fixture(); f["rows"][0]["g1"] = 1.25
        self.assert_invalid(f)

    def test_nan_G1_rejected(self):
        f = fixture(); f["rows"][0]["g1"] = "NaN"
        self.assert_invalid(f)

    def test_missing_sequence_type_rejected(self):
        f = fixture(); f["rows"][0]["label_sequence_type"] = "unknown"
        self.assert_invalid(f)

    def test_mixed_jump_and_samplewise_rejected(self):
        f = fixture(); f["rows"][0]["label_sequence_type"] = "jump_collapsed"
        self.assert_invalid(f)

    def test_sequence_boundary_required(self):
        f = fixture(); f["rows"][0]["epoch_boundary_reference"] = ""
        self.assert_invalid(f)

    def test_source_aligned_jump_type_admissible_synthetically(self):
        f = fixture()
        for row in f["rows"]:
            row["label_sequence_type"] = "jump_collapsed"
        result = audit(f)
        self.assertEqual(result["label_sequence_type"], "jump_collapsed")
        self.assertTrue(result["mixed_sequence_types_rejected"])

    def test_absent_length_rejected(self):
        f = fixture(); f["rows"][0]["sample_count"] = None
        self.assert_invalid(f)

    def test_false_boolean_sample_count_rejected(self):
        f = fixture(); f["rows"][0]["sample_count"] = True
        self.assert_invalid(f)

    def test_length_heterogeneity_reported(self):
        f = fixture(); f["rows"][0]["sample_count"] = 100
        result = audit(f)
        self.assertFalse(result["same_person_recording_lengths_equal_across_arms"])
        self.assertNotEqual(result["contrasts"]["DMT_vs_placebo"]["G1_raw"]["mean_exact"],
                            result["contrasts"]["DMT_vs_placebo"]["conditional_information_per_triple_nats"]["mean_exact"])

    def test_source_sha_mismatch_rejected(self):
        f = fixture(); f["source_toolbox_g1_blob"] = "0"*40
        self.assert_invalid(f)

    def test_real_mode_requires_provenance_review(self):
        f = fixture(); f["mode"] = "reviewed_original_source"; f["dataset_id"] = "zenodo:18850897"
        self.assert_invalid(f)

    def test_synthetic_review_receipt_rejected(self):
        f = fixture()
        self.assert_invalid(f, {"schema": RECEIPT_SCHEMA})

    def test_real_mode_requires_original_source_roster(self):
        f = fixture(); f["mode"] = "reviewed_original_source"; f["dataset_id"] = "zenodo:18850897"
        receipt = {"schema": RECEIPT_SCHEMA, "canonical_document_sha256": canonical_sha256(f),
                   "reviewer_reference": "synthetic review example only",
                   "rights_permission_reference": "synthetic rights example only",
                   "ethics_scope_reference": "synthetic ethics example only",
                   "condition_crosswalk_review_reference": "synthetic source map example",
                   "sequence_length_review_reference": "synthetic length example"}
        self.assert_invalid(f, receipt)

    def test_claim_ceilings(self):
        r = audit(fixture())
        self.assertFalse(r["direct_author_ARTool_ANOVA_reproduced"])
        self.assertFalse(r["source_permissions_independently_verified"])
        self.assertFalse(r["external_agent_ontology_established"])


if __name__ == "__main__":
    unittest.main()
