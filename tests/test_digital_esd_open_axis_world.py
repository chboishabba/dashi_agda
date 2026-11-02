"""Focused n-axis study-part ledger tests. Synthetic, no source-review promotion."""
import unittest

from interop_scripts.digital_esd.audit_open_axis_study_world import validate


def fixture():
    axes = [
        {"axis_ref": "participant-power", "meaning": "Who can make consequential decisions?"},
        {"axis_ref": "ecological-consequence", "meaning": "Ecological/material effects"},
        {"axis_ref": "time", "meaning": "Longitudinal and historical status"},
    ]
    parts = [
        {"source_ref": "source-A", "source_revision_ref": "shaA",
         "part_ref": "method", "part_kind": "component",
         "decomposition_receipt_ref": "reconstruction-A"},
        {"source_ref": "source-B", "source_revision_ref": "shaB",
         "part_ref": "inference", "part_kind": "component",
         "decomposition_receipt_ref": "reconstruction-B"},
    ]
    accounts = [
        {"source_ref": part["source_ref"], "part_ref": part["part_ref"],
         "axis_ref": axis["axis_ref"], "state": "not_yet_assessed",
         "reason": "Source-specific review is not complete",
         "review_work_ref": "question-for-review"}
        for part in parts for axis in axes
    ]
    return {
        "axis_registry_revision": "synthetic-test-v1",
        "part_taxonomy_revision": "synthetic-study-parts-v1",
        "required_part_kinds": ["component"],
        "axes": axes, "parts": parts, "accounts": accounts,
        "relations": [{
            "relation_ref": "question-not-empirical-join",
            "participants": [
                {"source_ref": "source-A", "part_ref": "method"},
                {"source_ref": "source-B", "part_ref": "inference"},
            ],
            "axes": ["participant-power", "ecological-consequence", "time"],
            "valence": {"kind": "balanced_ternary", "value": "zero"},
            "epistemic_status": "unresolved",
            "source_and_context_receipt_refs": ["test-only-hypothesis"],
        }],
    }


class StudyWorldAxisTests(unittest.TestCase):
    def test_every_part_every_axis_accounted_and_no_promotion(self):
        r = validate(fixture())
        self.assertEqual(r["axis_count"], 3)
        self.assertEqual(r["account_count"], 6)
        self.assertEqual(len(r["connected_components_over_declared_parts"]), 1)
        self.assertEqual(r["relation_arity_counts"], {2: 1})
        self.assertFalse(r["empirical_world_admitted"])

    def test_missing_axis_is_not_silent(self):
        item = fixture()
        item["accounts"].pop()
        with self.assertRaisesRegex(ValueError, "axis accounting incomplete"):
            validate(item)

    def test_new_required_study_part_kind_must_be_present_in_each_study(self):
        item = fixture()
        item["required_part_kinds"].append("researcher-epistemics")
        with self.assertRaisesRegex(ValueError, "missing declared required study part kinds"):
            validate(item)

    def test_new_axis_requires_reaccounting_all_parts(self):
        item = fixture()
        item["axes"].append({"axis_ref": "community-authority", "meaning": "Community veto"})
        with self.assertRaisesRegex(ValueError, "axis accounting incomplete: 2"):
            validate(item)

    def test_unmeasured_requires_source_scope_review(self):
        item = fixture()
        account = item["accounts"][0]
        account.update(state="unmeasured", missing_observation_ref="no observed measurement")
        with self.assertRaisesRegex(ValueError, "reviewed_source_scope_ref"):
            validate(item)
        account["reviewed_source_scope_ref"] = "reviewed-methods-and-results-scope"
        result = validate(item)
        self.assertEqual(result["evidence_state_counts"]["unmeasured"], 1)
        self.assertFalse(result["empirical_world_admitted"])

    def test_unreviewed_counts_prevent_closure(self):
        result = validate(fixture())
        self.assertEqual(result["unassessed_part_axis_count"], 6)
        self.assertFalse(result["all_part_axis_reviews_closed"])

    def test_author_report_pending_review_stays_unadmitted(self):
        item = fixture()
        item["accounts"][0].update(
            state="source_reported_pending_review",
            source_section_ref="published Method section",
            reported_observation_ref="author-reported response",
            review_debt_ref="SLR exact full-text span and independent review pending",
        )
        result = validate(item)
        self.assertEqual(
            result["evidence_state_counts"]["source_reported_pending_review"], 1
        )
        self.assertEqual(result["direct_reviewed_structural_receipt_count"], 0)
        self.assertFalse(result["empirical_world_admitted"])

    def test_pending_author_report_needs_actual_section(self):
        item = fixture()
        item["accounts"][0].update(state="source_reported_pending_review")
        with self.assertRaisesRegex(ValueError, "source_section_ref"):
            validate(item)

    def test_no_duplicate_account(self):
        item = fixture()
        item["accounts"].append(item["accounts"][0].copy())
        with self.assertRaisesRegex(ValueError, "duplicate part-axis"):
            validate(item)

    def test_direct_reviewed_cannot_be_unreceipted(self):
        item = fixture()
        account = item["accounts"][0]
        account.update(state="direct_reviewed")
        with self.assertRaisesRegex(ValueError, "reviewed_packet_ref"):
            validate(item)

    def test_reviewed_revision_must_match_study(self):
        item = fixture()
        account = item["accounts"][0]
        account.update(state="direct_reviewed",
                       **{key: key + "-value" for key in (
                           "reviewed_packet_ref", "reviewed_observation_ref",
                           "evidence_span_ref", "source_audit_observation_membership_ref",
                           "part_axis_relevance_review_ref",
                           "source_audit_admission_ref")})
        account["fulltext_revision_ref"] = "wrong"
        with self.assertRaisesRegex(ValueError, "revision != study"):
            validate(item)

    def test_unscored_candidate_is_not_a_ternary_zero(self):
        item = fixture()
        item["relations"][0]["valence"] = {"kind": "unscored", "value": None}
        item["relations"][0]["epistemic_status"] = "candidate"
        result = validate(item)
        self.assertFalse(result["empirical_world_admitted"])
        item["relations"][0]["epistemic_status"] = "reviewed"
        with self.assertRaisesRegex(ValueError, "cannot be promoted"):
            validate(item)

    def test_unscored_cannot_smuggle_numeric_zero(self):
        item = fixture()
        item["relations"][0]["valence"] = {"kind": "unscored", "value": 0}
        with self.assertRaisesRegex(ValueError, "cannot carry"):
            validate(item)

    def test_trit_is_not_epistemic_status(self):
        item = fixture()
        item["relations"][0]["epistemic_status"] = None
        with self.assertRaisesRegex(ValueError, "independent epistemic status"):
            validate(item)

    def test_any_relation_arity_supported(self):
        item = fixture()
        item["parts"].append({
            "source_ref": "source-C", "source_revision_ref": "shaC",
            "part_ref": "observer", "part_kind": "component",
            "decomposition_receipt_ref": "reconstruction-C",
        })
        for axis in item["axes"]:
            item["accounts"].append({
                "source_ref": "source-C", "part_ref": "observer",
                "axis_ref": axis["axis_ref"], "state": "inaccessible",
                "reason": "No permissible source disclosure",
                "access_constraint_ref": "privacy-gate",
            })
        item["relations"][0]["participants"].append({
            "source_ref": "source-C", "part_ref": "observer"})
        r = validate(item)
        self.assertEqual(r["relation_arity_counts"], {3: 1})
        self.assertFalse(r["empirical_world_admitted"])


if __name__ == "__main__":
    unittest.main()
