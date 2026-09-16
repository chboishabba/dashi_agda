#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_world_research_typed_route_frontier.py"
spec = importlib.util.spec_from_file_location("slr_world_research_typed_route_frontier", MODULE_PATH)
assert spec and spec.loader
frontier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(frontier)


class TypedRouteFrontierTests(unittest.TestCase):
    def test_selected_routes_replace_generic_qid_frontier_without_replanning(self) -> None:
        iteration = {
            "schema": "slr-world-research-iteration-v1",
            "semantic_closure_reference": "/tmp/old.json",
            "next_acquisition_obligations": [
                {"obligation_kind": "missing-language-surface", "qid": "Q1", "language": "fr", "candidate_only": True},
                {"obligation_kind": "follow-related-qid", "qid": "Q999", "candidate_only": True},
            ],
        }
        closure = {
            "schema": "slr-semantic-world-closure-v1",
            "pareto_support_coordinates_emitted": True,
            "acquisition_obligations": [
                {"obligation_kind": "follow-related-qid", "qid": "Q999", "candidate_only": True},
            ],
        }
        plan = {
            "selected_route_actions": [
                {
                    "action_id": "Q10:P279:Q20",
                    "source_qid": "Q10",
                    "target_qid": "Q20",
                    "property_id": "P279",
                    "route_family": "wikidata-subclass-parent",
                    "route_direction": "outbound",
                    "pareto_front_rank": 0,
                    "cross_language_gap_coverage": 3,
                    "source_surface_support": 2,
                    "root_qid_support": 1,
                }
            ]
        }
        welded = frontier.weld_typed_route_frontier(iteration, closure, plan)
        obligations = welded["closure"]["acquisition_obligations"]
        related = [x for x in obligations if x.get("obligation_kind") == "follow-related-qid"]
        self.assertEqual([x["qid"] for x in related], ["Q20"])
        self.assertEqual(related[0]["route_property_id"], "P279")
        self.assertTrue(welded["closure"]["typed_route_frontier_locked"])
        self.assertEqual(welded["iteration"]["semantic_closure_reference"], "__SYNTHETIC_TYPED_ROUTE_CLOSURE__")
        self.assertTrue(welded["iteration"]["typed_route_frontier_locked"])

    def test_missing_surfaces_are_preserved_separately(self) -> None:
        iteration = {
            "schema": "slr-world-research-iteration-v1",
            "next_acquisition_obligations": [
                {"obligation_kind": "missing-language-surface", "qid": "Q1", "language": "simple", "candidate_only": True}
            ],
        }
        closure = {"schema": "slr-semantic-world-closure-v1", "pareto_support_coordinates_emitted": True}
        plan = {"selected_route_actions": []}
        welded = frontier.weld_typed_route_frontier(iteration, closure, plan)
        self.assertEqual(welded["closure"]["acquisition_obligations"][0]["obligation_kind"], "missing-language-surface")
        self.assertFalse(welded["closure"]["semantic_promotion"])


if __name__ == "__main__":
    unittest.main()
