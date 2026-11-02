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
         "part_ref": "method", "part_kind": "method",
         "decomposition_receipt_ref": "reconstruction-A"},
        {"source_ref": "source-B", "source_revision_ref": "shaB",
         "part_ref": "inference", "part_kind": "inference",
         "decomposition_receipt_ref": "reconstruction-B"},
    ]
    accounts = [
        {"source_ref": part["source_ref"], "part_ref": part["part_ref"],
         "axis_ref": axis["axis_ref"], "state": "unmeasured",
         "reason": "No demonstrated source-specific observation",
         "missing_observation_ref": "question-for-review"}
        for part in parts for axis in axes
    ]
    return {
        "axis_registry_revision": "synthetic-test-v1",
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

    def test_new_axis_requires_reaccounting_all_parts(self):
        item = fixture()
        item["axes"].append({"axis_ref": "community-authority", "meaning": "Community veto"})
        with self.assertRaisesRegex(ValueError, "axis accounting incomplete: 2"):
            validate(item)

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

    def test_trit_is_not_epistemic_status(self):
        item = fixture()
        item["relations"][0]["epistemic_status"] = None
        with self.assertRaisesRegex(ValueError, "independent epistemic status"):
            validate(item)

    def test_any_relation_arity_supported(self):
        item = fixture()
        item["parts"].append({
            "source_ref": "source-C", "source_revision_ref": "shaC",
            "part_ref": "observer", "part_kind": "epistemic-observer",
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
