#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_world_research_route_pareto.py"
spec = importlib.util.spec_from_file_location("slr_world_research_route_pareto", MODULE_PATH)
assert spec and spec.loader
route = importlib.util.module_from_spec(spec)
spec.loader.exec_module(route)


class WorldResearchRouteParetoTests(unittest.TestCase):
    def test_typed_property_routes_preserve_pid_and_direction(self) -> None:
        graph = {
            "schema": "slr-wikimedia-world-follow-v1",
            "item_property_edges": [
                {"source": "Q1", "property_id": "P279", "target": "Q2", "edge_class": "parent"},
                {"source": "Q3", "property_id": "P31", "target": "Q2", "edge_class": "parent"},
                {"source": "Q1", "property_id": "P361", "target": "Q4", "edge_class": "parent"},
            ],
            "first_link_candidates": [],
        }
        closure = {
            "schema": "slr-semantic-world-closure-v1",
            "acquisition_obligations": [
                {
                    "obligation_kind": "follow-related-qid",
                    "qid": "Q2",
                    "cross_language_gap_coverage": 5,
                    "source_surface_support": 3,
                    "root_qid_support": 2,
                    "typed_wikidata_property_target": True,
                    "candidate_only": True,
                },
                {
                    "obligation_kind": "follow-related-qid",
                    "qid": "Q4",
                    "cross_language_gap_coverage": 2,
                    "source_surface_support": 1,
                    "root_qid_support": 1,
                    "typed_wikidata_property_target": True,
                    "candidate_only": True,
                },
            ],
        }
        actions = route.build_route_actions(closure, graph, yield_history=None)
        triples = {(a["source_qid"], a["property_id"], a["target_qid"], a["route_family"]) for a in actions}
        self.assertIn(("Q1", "P279", "Q2", "wikidata-subclass-parent"), triples)
        self.assertIn(("Q3", "P31", "Q2", "wikidata-instance-class"), triples)
        self.assertIn(("Q1", "P361", "Q4", "wikidata-part-of"), triples)
        self.assertTrue(all(a["typed_property_is_claim_truth"] is False for a in actions))

    def test_current_first_link_is_navigation_not_historical_ibrahim_equivalence(self) -> None:
        graph = {
            "schema": "slr-wikimedia-world-follow-v1",
            "item_property_edges": [],
            "first_link_candidates": [
                {
                    "from_qid": "Q1",
                    "candidate_qid": "Q8",
                    "edge_kind": "current-first-mainspace-link-candidate",
                    "ibrahim_parser_equivalence_paid": False,
                    "historical_snapshot_identity_paid": False,
                }
            ],
        }
        closure = {
            "schema": "slr-semantic-world-closure-v1",
            "acquisition_obligations": [
                {
                    "obligation_kind": "follow-related-qid",
                    "qid": "Q8",
                    "cross_language_gap_coverage": 4,
                    "source_surface_support": 2,
                    "root_qid_support": 1,
                    "typed_wikidata_property_target": False,
                    "candidate_only": True,
                }
            ],
        }
        action = next(a for a in route.build_route_actions(closure, graph, yield_history=None) if a["route_family"] == "wikipedia-first-link")
        self.assertFalse(action["ibrahim_parser_equivalence_paid"])
        self.assertFalse(action["historical_snapshot_identity_paid"])
        self.assertFalse(action["route_creates_claim_truth"])

    def test_route_pareto_uses_minimize_and_maximize_axes_without_scalarization(self) -> None:
        rows = [
            {
                "action_id": "a",
                "target_qid": "Q10",
                "cross_language_gap_coverage": 3,
                "source_surface_support": 2,
                "root_qid_support": 1,
                "typed_property_support": 1,
                "route_specificity": 4,
                "prior_contracted_old_gaps": 0,
                "prior_retired_obligations": 0,
                "prior_new_gap_atoms": 100,
                "prior_network_requests": 10,
            },
            {
                "action_id": "b",
                "target_qid": "Q20",
                "cross_language_gap_coverage": 3,
                "source_surface_support": 2,
                "root_qid_support": 1,
                "typed_property_support": 1,
                "route_specificity": 4,
                "prior_contracted_old_gaps": 2,
                "prior_retired_obligations": 5,
                "prior_new_gap_atoms": 20,
                "prior_network_requests": 5,
            },
        ]
        ranked = route.pareto_rank_actions(rows)
        self.assertEqual(ranked[0]["action_id"], "b")
        self.assertEqual(ranked[0]["pareto_front_rank"], 0)
        self.assertGreater(ranked[1]["pareto_front_rank"], 0)
        self.assertFalse(ranked[0]["pareto_dimensions_scalarized"])

    def test_one_target_gets_one_selected_route_and_seed_retains_route_metadata(self) -> None:
        actions = [
            {
                "action_id": "Q1:P279:Q2",
                "source_qid": "Q1",
                "property_id": "P279",
                "target_qid": "Q2",
                "route_family": "wikidata-subclass-parent",
                "route_direction": "outbound",
                "cross_language_gap_coverage": 5,
                "source_surface_support": 2,
                "root_qid_support": 1,
                "typed_property_support": 1,
                "route_specificity": 5,
                "prior_contracted_old_gaps": 0,
                "prior_retired_obligations": 0,
                "prior_new_gap_atoms": 0,
                "prior_network_requests": 0,
                "candidate_only": True,
            },
            {
                "action_id": "Q3:P31:Q2",
                "source_qid": "Q3",
                "property_id": "P31",
                "target_qid": "Q2",
                "route_family": "wikidata-instance-class",
                "route_direction": "outbound",
                "cross_language_gap_coverage": 4,
                "source_surface_support": 2,
                "root_qid_support": 1,
                "typed_property_support": 1,
                "route_specificity": 5,
                "prior_contracted_old_gaps": 0,
                "prior_retired_obligations": 0,
                "prior_new_gap_atoms": 0,
                "prior_network_requests": 0,
                "candidate_only": True,
            },
        ]
        selected = route.select_route_actions(actions, max_targets=2)
        self.assertEqual(len(selected), 1)
        seeds = route.seed_rows(selected, iteration_index=3)
        self.assertEqual(seeds[0]["qid"], "Q2")
        self.assertIn(seeds[0]["route_family"], {"wikidata-subclass-parent", "wikidata-instance-class"})
        self.assertFalse(seeds[0]["semantic_promotion"])


if __name__ == "__main__":
    unittest.main()
