#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_world_research_gap_flow.py"
spec = importlib.util.spec_from_file_location("slr_world_research_gap_flow", MODULE_PATH)
assert spec and spec.loader
gap_flow = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gap_flow)


class WorldResearchGapFlowTests(unittest.TestCase):
    def test_distinguishes_contracted_persisting_and_new_gaps(self) -> None:
        previous = {
            "schema": "slr-semantic-world-closure-v1",
            "canonical_atoms": [
                {"atom_id": "qid:Q1", "kind": "qid", "qid": "Q1"},
                {"atom_id": "wiki-link:Q1:Q2", "kind": "wiki-link", "subject_qid": "Q1", "object_qid": "Q2"},
            ],
            "gaps": [
                {"surface_id": "Q1:en", "missing_atom_ids": ["wiki-link:Q1:Q2"]},
                {"surface_id": "Q1:fr", "missing_atom_ids": ["wiki-link:Q1:Q2"]},
            ],
            "acquisition_obligations": [
                {"obligation_kind": "follow-related-qid", "qid": "Q2", "candidate_only": True}
            ],
        }
        current = {
            "schema": "slr-semantic-world-closure-v1",
            "canonical_atoms": [
                {"atom_id": "qid:Q1", "kind": "qid", "qid": "Q1"},
                {"atom_id": "wiki-link:Q1:Q2", "kind": "wiki-link", "subject_qid": "Q1", "object_qid": "Q2"},
                {"atom_id": "qid:Q2", "kind": "qid", "qid": "Q2"},
                {"atom_id": "wiki-link:Q2:Q3", "kind": "wiki-link", "subject_qid": "Q2", "object_qid": "Q3"},
            ],
            "gaps": [
                {"surface_id": "Q1:fr", "missing_atom_ids": ["wiki-link:Q1:Q2"]},
                {"surface_id": "Q2:en", "missing_atom_ids": ["wiki-link:Q2:Q3"]},
            ],
            "acquisition_obligations": [
                {"obligation_kind": "follow-related-qid", "qid": "Q3", "candidate_only": True}
            ],
        }
        flow = gap_flow.compare_closures(previous, current, selected_qids=["Q2"])
        self.assertEqual(flow["prior_gap_atoms"], 2)
        self.assertEqual(flow["contracted_gap_atoms"], 1)
        self.assertEqual(flow["persisting_gap_atoms"], 1)
        self.assertEqual(flow["new_gap_atoms"], 1)
        self.assertEqual(flow["net_gap_delta"], 0)
        self.assertEqual(flow["retired_obligations"], 1)
        self.assertEqual(flow["new_obligations"], 1)
        self.assertEqual(flow["persisting_obligations"], 0)
        self.assertEqual(flow["atoms_added_per_selected_qid"], {"Q2": 2})
        self.assertFalse(flow["net_gap_growth_implies_no_contraction"])

    def test_net_gap_growth_can_coexist_with_real_contraction(self) -> None:
        previous = {
            "schema": "slr-semantic-world-closure-v1",
            "canonical_atoms": [],
            "gaps": [{"surface_id": "Q1:en", "missing_atom_ids": ["a", "b"]}],
            "acquisition_obligations": [],
        }
        current = {
            "schema": "slr-semantic-world-closure-v1",
            "canonical_atoms": [],
            "gaps": [{"surface_id": "Q1:en", "missing_atom_ids": ["b", "c", "d", "e"]}],
            "acquisition_obligations": [],
        }
        flow = gap_flow.compare_closures(previous, current, selected_qids=[])
        self.assertEqual(flow["contracted_gap_atoms"], 1)
        self.assertEqual(flow["new_gap_atoms"], 3)
        self.assertEqual(flow["net_gap_delta"], 2)
        self.assertFalse(flow["net_gap_growth_implies_no_contraction"])


if __name__ == "__main__":
    unittest.main()
