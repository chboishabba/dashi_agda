#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_article_pnf_semantic_weld.py"
spec = importlib.util.spec_from_file_location("slr_article_pnf_semantic_weld", MODULE_PATH)
assert spec and spec.loader
weld = importlib.util.module_from_spec(spec)
spec.loader.exec_module(weld)


class ArticlePNFSemanticWeldTests(unittest.TestCase):
    def test_pnf_atom_is_observed_only_on_its_source_manifestation(self) -> None:
        closure = {
            "schema": "slr-semantic-world-closure-v1",
            "canonical_atoms": [{"atom_id": "qid:Q1", "kind": "qid", "qid": "Q1"}],
            "surface_semantic_closure_atom_ids": ["qid:Q1"],
            "surfaces": [
                {"surface_id": "Q1:en", "qid": "Q1", "language": "en", "status": "observed", "observed_atom_ids": ["qid:Q1"]},
                {"surface_id": "Q1:fr", "qid": "Q1", "language": "fr", "status": "observed", "observed_atom_ids": ["qid:Q1"]},
            ],
            "gaps": [],
            "propagated_views": [],
            "acquisition_obligations": [],
            "summary": {},
            "candidate_only": True,
            "semantic_promotion": False,
        }
        article = {
            "schema": "slr-wikipedia-article-pnf-world-producer-v1",
            "article_manifestations": [
                {"qid": "Q1", "language": "en", "revision_id": 10, "source_text_sha256": "abc"}
            ],
            "pnf_candidates": [
                {"claim_candidate_id": "pnf-candidate:x", "document_ref": "wiki:Q1:en:10", "sentence_index": 0,
                 "subject_terms": ["A"], "predicate_lemmas": ["be"], "object_terms": ["B"], "negated": False,
                 "sentence_text_sha256": "sent", "claim_truth_promoted": False}
            ],
            "qid_pnf_weld_candidates": [
                {"qid": "Q1", "document_ref": "wiki:Q1:en:10", "claim_candidate_id": "pnf-candidate:x",
                 "surface_qid_identity_paid": True, "span_entity_identity_paid": False,
                 "qid_property_weld_paid": False, "claim_semantic_equivalence_paid": False}
            ],
            "candidate_only": True,
            "semantic_promotion": False,
        }
        out = weld.weld_article_pnf(closure, article)
        atom_id = "pnf:pnf-candidate:x"
        en = next(x for x in out["surfaces"] if x["surface_id"] == "Q1:en")
        fr = next(x for x in out["surfaces"] if x["surface_id"] == "Q1:fr")
        self.assertIn(atom_id, en["observed_atom_ids"])
        self.assertNotIn(atom_id, fr["observed_atom_ids"])
        fr_gap = next(x for x in out["gaps"] if x["surface_id"] == "Q1:fr")
        self.assertIn(atom_id, fr_gap["missing_atom_ids"])
        propagated = next(x for x in out["propagated_views"] if x["target_surface_id"] == "Q1:fr" and x["atom_id"] == atom_id)
        self.assertFalse(propagated["target_surface_asserted"])
        self.assertFalse(propagated["claim_semantic_equivalence_paid"])

    def test_weld_keeps_parser_and_claim_truth_firewalls(self) -> None:
        closure = {"schema": "slr-semantic-world-closure-v1", "canonical_atoms": [], "surface_semantic_closure_atom_ids": [], "surfaces": [], "gaps": [], "propagated_views": [], "acquisition_obligations": [], "summary": {}, "candidate_only": True, "semantic_promotion": False}
        article = {"schema": "slr-wikipedia-article-pnf-world-producer-v1", "article_manifestations": [], "pnf_candidates": [], "qid_pnf_weld_candidates": [], "candidate_only": True, "semantic_promotion": False}
        out = weld.weld_article_pnf(closure, article)
        self.assertFalse(out["article_pnf_creates_claim_truth"])
        self.assertFalse(out["parser_output_creates_ontology_truth"])
        self.assertFalse(out["semantic_promotion"])


if __name__ == "__main__":
    unittest.main()
