"""Original oldid/pageid/wikitext and first-qualified-link adversarial tests."""
from __future__ import annotations
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from ibrahim_original_revision_audit import audit_revision


def revision(wikitext="Alpha [[Awareness]] beta [[Consciousness]]"):
    return {
        "batchcomplete": True,
        "query": {"pages": [{
            "pageid": 123,
            "title": "Original article",
            "revisions": [{
                "revid": 456,
                "timestamp": "2016-06-01T00:00:00Z",
                "slots": {"main": {"contentmodel": "wikitext", "content": wikitext}},
            }],
        }]},
    }


def encode(data):
    raw = json.dumps(data, sort_keys=True, ensure_ascii=False).encode("utf-8")
    return raw, sha256(raw).hexdigest()


class OriginalRevisionAuditTest(unittest.TestCase):
    def audit(self, data, **changes):
        raw, digest = encode(data)
        kwargs = dict(raw=raw, pinned_raw_sha256=digest, oldid=456,
                      pageid=123, expected_title="Original article")
        kwargs.update(changes)
        return audit_revision(**kwargs)

    def test_actual_first_qualified_span_from_original_wikitext(self):
        receipt = self.audit(revision())
        first = receipt["first_qualified_link"]
        self.assertEqual(first["selected_target"], "Awareness")
        self.assertEqual(first["raw_link"], "[[Awareness]]")
        self.assertEqual(first["selected_span"], [6, 19])
        self.assertFalse(receipt["zelph_edge_equals_wikipedia_first_link_proved"])
        self.assertFalse(receipt["historical_original_author_code_executed"])

    def test_original_no_qualified_link_does_not_prove_graph_absence(self):
        receipt = self.audit(revision("No eligible link here."))
        self.assertIsNone(receipt["first_qualified_link"])
        self.assertFalse(receipt["wikidata_qid_same_object_authenticated"])

    def test_pageid_revision_and_title_strict(self):
        for key, value in (("pageid", 124), ("title", "Other")):
            data = revision()
            data["query"]["pages"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.audit(data)
        data = revision()
        data["query"]["pages"][0]["revisions"][0]["revid"] += 1
        with self.assertRaises(ValueError):
            self.audit(data)

    def test_missing_or_non_wikitext_main_slot_rejected(self):
        for variant in ("missing", "nontext"):
            data = revision()
            main = data["query"]["pages"][0]["revisions"][0]
            if variant == "missing":
                main["slots"] = {}
            else:
                main["slots"]["main"]["contentmodel"] = "json"
            with self.assertRaises(ValueError):
                self.audit(data)

    def test_raw_sha_cannot_be_self_relabelled(self):
        raw, digest = encode(revision())
        with self.assertRaises(ValueError):
            audit_revision(raw=raw, pinned_raw_sha256="0" * 64,
                           oldid=456, pageid=123)

    def test_expected_target_drift_refused(self):
        with self.assertRaises(ValueError):
            self.audit(revision(), expected_target="Consciousness")

    def test_reject_ambiguous_page_or_revision_sets(self):
        data = revision()
        data["query"]["pages"].append(deepcopy(data["query"]["pages"][0]))
        with self.assertRaises(ValueError):
            self.audit(data)
        data = revision()
        data["query"]["pages"][0]["revisions"].append(
            deepcopy(data["query"]["pages"][0]["revisions"][0]))
        with self.assertRaises(ValueError):
            self.audit(data)

    def test_duplicate_json_keys_rejected(self):
        raw = (b'{"query":{"pages":[]},"query":{"pages":[]}}')
        with self.assertRaises(ValueError):
            audit_revision(raw=raw, pinned_raw_sha256=sha256(raw).hexdigest(),
                           oldid=456, pageid=123)


if __name__ == "__main__":
    unittest.main()
