"""Exact source-level synthetic acceptance and leakage regressions; no Erowid records."""
import copy
import unittest

from scripts.evaluate_dmt_temporal_motifs import (
    SCHEMA, RECEIPT_SCHEMA, canonical_sha256, evaluate, validate)


def fixture():
    source = "synthetic:cycle-example"
    return {
        "schema": SCHEMA, "mode": "synthetic", "observation_unit": "report",
        "source_collection_id": source,
        "motif_vocabulary": ["lattice", "tunnel", "face"],
        "governance": {
            "codebook_reference": "synthetic constructed 3-motif basis",
            "chronology_method_reference": "synthetic stipulated ordinal steps",
            "source_identity_reference": "synthetic local toy only",
            "independence_review_reference": "synthetic known groups"},
        "reports": [{
            "report_id": str(i), "independence_unit_id": group,
            "source_collection_id": source, "chronology_verified": True,
            "events": [{"ordinal": j, "motif": motif} for j, motif in enumerate(sequence)]}
            for i, (group, sequence) in enumerate((
                ("A", ["lattice", "tunnel", "face"]),
                ("B", ["lattice", "face", "tunnel"]),
                ("C", ["face", "tunnel", "lattice"])))],
    }


class TestTemporalMotifs(unittest.TestCase):
    def assert_invalid(self, changed):
        with self.assertRaises(ValueError):
            validate(changed)

    def test_synthetic_exact_ratio(self):
        output = evaluate(fixture())
        self.assertEqual(output["report_count"], 3)
        self.assertEqual(output["independence_units"], 3)
        self.assertEqual(sum(x["held_out_transitions"] for x in output["folds"]), 6)
        self.assertFalse(output["independent_external_agent_inferred"])
        for fold in output["folds"]:
            self.assertIn("/", fold["temporal_vs_static_ratio_exact"] + "/")

    def test_missing_governance(self):
        f = fixture(); f["governance"]["codebook_reference"] = ""
        self.assert_invalid(f)

    def test_synthetic_cannot_pose_as_source(self):
        f = fixture(); f["source_collection_id"] = "Erowid"
        self.assert_invalid(f)

    def test_rights_reference_alone_does_not_admit_real(self):
        f = fixture(); f["mode"] = "authorized_research"
        with self.assertRaises(ValueError):
            evaluate(f)

    def test_tampered_reviewer_receipt_denied(self):
        f = fixture(); f["mode"] = "authorized_research"
        receipt = self.receipt(f)
        receipt["dataset_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            evaluate(f, receipt)

    @staticmethod
    def receipt(f):
        return {"schema": RECEIPT_SCHEMA, "dataset_sha256": canonical_sha256(f),
                "source_collection_id": f["source_collection_id"],
                "rights_holder": "EXAMPLE RIGHTS HOLDER -- SYNTHETIC ONLY",
                "permission_document_sha256": "a" * 64,
                "reviewer_reference": "synthetic test reviewer",
                "scope_reference": "synthetic test scope",
                "ai_processing_in_scope": True,
                "temporal_analysis_in_scope": True}

    def test_synthetic_source_cannot_relabel_with_receipt(self):
        f = fixture(); f["mode"] = "authorized_research"
        with self.assertRaises(ValueError):
            evaluate(f, self.receipt(f))

    def test_attested_real_execution_is_not_permission_proof(self):
        f = fixture(); f["mode"] = "authorized_research"
        f["source_collection_id"] = "controlled:illustrative-nonhuman-only"
        for report in f["reports"]:
            report["source_collection_id"] = f["source_collection_id"]
        out = evaluate(f, self.receipt(f))
        self.assertEqual(out["independence_units"], 3)
        self.assertTrue(out["permission_legality_not_automatically_established"])
        self.assertEqual(out["admission_status"], "separate_reviewer_attestation_required_external_verification")

    def test_explicit_scope_required(self):
        f = fixture(); f["mode"] = "authorized_research"
        receipt = self.receipt(f); receipt["ai_processing_in_scope"] = False
        with self.assertRaises(ValueError):
            evaluate(f, receipt)

    def test_chronology_gate(self):
        f = fixture(); f["reports"][0]["chronology_verified"] = False
        self.assert_invalid(f)

    def test_duplicate_report_gate(self):
        f = fixture(); f["reports"][1]["report_id"] = "0"
        self.assert_invalid(f)

    def test_unordered_events_gate(self):
        f = fixture(); f["reports"][0]["events"][1]["ordinal"] = 0
        self.assert_invalid(f)

    def test_raw_report_rejected(self):
        f = fixture(); f["reports"][0]["raw_text"] = "DO NOT STORE REPORT TEXT"
        self.assert_invalid(f)

    def test_static_counts_not_chronology(self):
        f = fixture(); f["reports"][0].pop("events")
        f["reports"][0]["category_counts"] = {"lattice": 2}
        self.assert_invalid(f)

    def test_predeclared_vocabulary(self):
        f = fixture(); f["reports"][0]["events"][0]["motif"] = "unregistered"
        self.assert_invalid(f)

    def test_cross_source_rejected(self):
        f = fixture(); f["reports"][0]["source_collection_id"] = "other"
        self.assert_invalid(f)

    def test_group_holdout_excludes_all_dependent_reports(self):
        f = fixture()
        duplicate = copy.deepcopy(f["reports"][0]); duplicate["report_id"] = "3"
        f["reports"].append(duplicate)
        out = evaluate(f)
        self.assertEqual(out["independence_units"], 3)
        self.assertEqual(next(x for x in out["folds"] if x["held_out_independence_unit_id"] == "A")["held_out_report_count"], 2)

    def test_report_permutation_invariance(self):
        f = fixture(); g = copy.deepcopy(f)
        g["reports"].reverse()
        self.assertEqual(evaluate(f)["folds"], evaluate(g)["folds"])

    def test_boolean_ordinal_rejected(self):
        f = fixture(); f["reports"][0]["events"][0]["ordinal"] = True
        self.assert_invalid(f)

    def test_single_independence_unit_rejected(self):
        f = fixture()
        for r in f["reports"]:
            r["independence_unit_id"] = "same person"
        self.assert_invalid(f)

    def test_source_only_receipt_not_real_observation(self):
        f = fixture(); result = evaluate(f)
        self.assertTrue(result["held_out_predictive_comparison_only"])
        self.assertTrue(result["permission_legality_not_automatically_established"])
        self.assertFalse(result["measured_neural_mechanism"])


if __name__ == "__main__":
    unittest.main()
