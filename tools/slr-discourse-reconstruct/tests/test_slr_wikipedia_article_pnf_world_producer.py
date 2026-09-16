#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_wikipedia_article_pnf_world_producer.py"
spec = importlib.util.spec_from_file_location("slr_wikipedia_article_pnf_world_producer", MODULE_PATH)
assert spec and spec.loader
producer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(producer)


class WikipediaArticlePNFWorldProducerTests(unittest.TestCase):
    def test_dependency_rows_project_to_explicit_pnf_roles(self) -> None:
        rows = [
            {"i": 0, "text": "Bush", "lemma": "Bush", "dep": "nsubj", "head_i": 1, "idx": 0},
            {"i": 1, "text": "signed", "lemma": "sign", "dep": "ROOT", "head_i": 1, "idx": 5},
            {"i": 2, "text": "the", "lemma": "the", "dep": "det", "head_i": 3, "idx": 12},
            {"i": 3, "text": "law", "lemma": "law", "dep": "dobj", "head_i": 1, "idx": 16},
            {"i": 4, "text": "not", "lemma": "not", "dep": "neg", "head_i": 1, "idx": 20},
        ]
        candidate = producer.pnf_candidate_from_dependency_rows(
            rows,
            document_ref="wiki:Q1:en:123",
            sentence_index=0,
            sentence_start=0,
            sentence_end=23,
            sentence_sha256="abc",
        )
        self.assertEqual(candidate["predicate_lemmas"], ["sign"])
        self.assertEqual(candidate["subject_terms"], ["Bush"])
        self.assertEqual(candidate["object_terms"], ["law"])
        self.assertTrue(candidate["negated"])
        self.assertEqual(candidate["role_counts"]["predicate"], 1)
        self.assertFalse(candidate["claim_truth_promoted"])
        self.assertFalse(candidate["parser_output_is_ontology_truth"])

    def test_article_manifestation_requires_revision_and_source_hash(self) -> None:
        manifestation = producer.article_manifestation(
            qid="Q207",
            language="en",
            title="George W. Bush",
            pageid=123,
            revid=456,
            revision_timestamp="2026-09-12T00:00:00Z",
            revision_sha1="deadbeef",
            text="George W. Bush was president.",
        )
        self.assertEqual(manifestation["revision_id"], 456)
        self.assertEqual(len(manifestation["source_text_sha256"]), 64)
        self.assertTrue(manifestation["revision_pinned"])
        self.assertFalse(manifestation["article_text_creates_claim_truth"])

    def test_surface_qid_does_not_weld_span_entity_identity(self) -> None:
        weld = producer.qid_pnf_weld_candidate(
            qid="Q207",
            document_ref="wiki:Q207:en:456",
            claim_candidate_id="claim:1",
        )
        self.assertTrue(weld["surface_qid_identity_paid"])
        self.assertFalse(weld["span_entity_identity_paid"])
        self.assertFalse(weld["qid_property_weld_paid"])
        self.assertFalse(weld["claim_semantic_equivalence_paid"])

    def test_nat_source_unit_uses_same_producer_abi(self) -> None:
        row = producer.source_unit_manifestation(
            source_unit_ref="unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01",
            source_kind="wikidata-user-sandbox",
            language="en",
            revision_ref="provided_snapshot_2026-04-01",
            text="evaluate migration for 22514 statements on items that are instances of business",
        )
        self.assertEqual(row["producer_abi"], producer.PRODUCER_ABI)
        self.assertEqual(row["source_unit_ref"], "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01")
        self.assertFalse(row["source_unit_text_creates_migration_truth"])

    def test_article_payload_emits_compact_world_store_ndjson_without_promotion(self) -> None:
        payload = {
            "article_manifestations": [{
                "qid": "Q207", "language": "en", "revision_id": 456,
                "manifestation_kind": "wikipedia-revision-text",
                "source_text_sha256": "abc", "candidate_only": True,
                "semantic_promotion": False,
            }],
            "pnf_candidates": [{
                "claim_candidate_id": "pnf-candidate:1",
                "document_ref": "wiki:Q207:en:456",
                "candidate_only": True,
                "semantic_promotion": False,
            }],
        }
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "world-store.ndjson"
            count = producer.write_world_store_ndjson(payload, path, iteration_index=4)
            rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]
        self.assertEqual(count, 2)
        self.assertEqual([r["kind"] for r in rows], ["source_manifestation", "pnf_candidate"])
        self.assertEqual(rows[0]["id"], "wiki:Q207:en:456")
        self.assertEqual(rows[1]["source_manifestation_id"], "wiki:Q207:en:456")
        self.assertTrue(all(r["payload"]["candidate_only"] for r in rows))
        self.assertTrue(all(not r["payload"]["semantic_promotion"] for r in rows))


if __name__ == "__main__":
    unittest.main()
