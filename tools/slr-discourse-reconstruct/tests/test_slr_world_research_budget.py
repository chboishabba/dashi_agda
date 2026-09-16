#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_world_research_budget.py"
spec = importlib.util.spec_from_file_location("slr_world_research_budget", MODULE_PATH)
assert spec and spec.loader
budget = importlib.util.module_from_spec(spec)
spec.loader.exec_module(budget)


class WorldResearchBudgetTests(unittest.TestCase):
    def test_missing_language_surfaces_rank_before_related_qids_and_use_separate_budgets(self) -> None:
        obligations = [
            {"obligation_kind": "follow-related-qid", "qid": "Q30", "candidate_only": True},
            {"obligation_kind": "missing-language-surface", "qid": "Q1", "language": "fr", "candidate_only": True},
            {"obligation_kind": "follow-related-qid", "qid": "Q20", "candidate_only": True},
            {"obligation_kind": "missing-language-surface", "qid": "Q1", "language": "de", "candidate_only": True},
            {"obligation_kind": "follow-related-qid", "qid": "Q20", "candidate_only": True},
        ]
        plan = budget.plan_frontier(obligations, max_new_qids=1, max_missing_surfaces=2)
        self.assertEqual([x["language"] for x in plan["selected_missing_surfaces"]], ["de", "fr"])
        self.assertEqual([x["qid"] for x in plan["selected_related_qids"]], ["Q20"])
        self.assertEqual(plan["summary"]["deduplicated_follow_related_qids"], 2)
        self.assertEqual(plan["summary"]["selected_missing_surfaces"], 2)
        self.assertEqual(plan["summary"]["selected_related_qids"], 1)

    def test_pareto_front_beats_lexical_qid_order_without_scalarization(self) -> None:
        obligations = [
            {
                "obligation_kind": "follow-related-qid",
                "qid": "Q10",
                "cross_language_gap_coverage": 1,
                "source_surface_support": 1,
                "root_qid_support": 1,
                "typed_wikidata_property_target": False,
                "candidate_only": True,
            },
            {
                "obligation_kind": "follow-related-qid",
                "qid": "Q20",
                "cross_language_gap_coverage": 7,
                "source_surface_support": 4,
                "root_qid_support": 2,
                "typed_wikidata_property_target": True,
                "candidate_only": True,
            },
        ]
        plan = budget.plan_frontier(obligations, max_new_qids=1, max_missing_surfaces=0)
        selected = plan["selected_related_qids"]
        self.assertEqual([x["qid"] for x in selected], ["Q20"])
        self.assertEqual(selected[0]["pareto_front_rank"], 0)
        self.assertFalse(plan["pareto_dimensions_scalarized"])
        self.assertFalse(plan["frontier_rank_is_truth_rank"])

    def test_incomparable_candidates_share_front_and_qid_only_breaks_tie(self) -> None:
        obligations = [
            {
                "obligation_kind": "follow-related-qid",
                "qid": "Q30",
                "cross_language_gap_coverage": 8,
                "source_surface_support": 1,
                "root_qid_support": 1,
                "typed_wikidata_property_target": False,
                "candidate_only": True,
            },
            {
                "obligation_kind": "follow-related-qid",
                "qid": "Q20",
                "cross_language_gap_coverage": 2,
                "source_surface_support": 4,
                "root_qid_support": 2,
                "typed_wikidata_property_target": True,
                "candidate_only": True,
            },
        ]
        plan = budget.plan_frontier(obligations, max_new_qids=2, max_missing_surfaces=0)
        selected = plan["selected_related_qids"]
        self.assertEqual([x["pareto_front_rank"] for x in selected], [0, 0])
        self.assertEqual([x["qid"] for x in selected], ["Q20", "Q30"])

    def test_zero_budget_stops_without_claiming_consumer_closure(self) -> None:
        obligations = [{"obligation_kind": "follow-related-qid", "qid": "Q2", "candidate_only": True}]
        plan = budget.plan_frontier(obligations, max_new_qids=0, max_missing_surfaces=0)
        self.assertEqual(plan["stop_reason"], "budget-exhausted-before-acquisition")
        self.assertFalse(plan["consumer_closure_paid"])
        self.assertFalse(plan["semantic_promotion"])

    def test_seed_rows_are_explicit_qid_candidates_only(self) -> None:
        plan = budget.plan_frontier(
            [{"obligation_kind": "follow-related-qid", "qid": "Q42", "candidate_only": True}],
            max_new_qids=2,
            max_missing_surfaces=0,
        )
        rows = budget.seed_rows(plan, iteration_index=3)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["qid"], "Q42")
        self.assertEqual(rows[0]["seed_state"], "budgeted-follow-related-qid")
        self.assertFalse(rows[0]["semantic_promotion"])

    def test_missing_surface_attempt_history_prevents_infinite_retry(self) -> None:
        obligations = [
            {"obligation_kind": "missing-language-surface", "qid": "Q1", "language": "simple", "candidate_only": True}
        ]
        first = budget.plan_frontier(obligations, max_new_qids=0, max_missing_surfaces=1)
        history = budget.updated_attempt_history(None, first, 1)
        second = budget.plan_frontier(
            obligations,
            max_new_qids=0,
            max_missing_surfaces=1,
            attempted_missing=set(history["attempted_missing_surface_keys"]),
        )
        self.assertEqual(second["summary"]["actionable_missing_surfaces"], 0)
        self.assertEqual(second["stop_reason"], "frontier-exhausted-or-already-attempted")
        self.assertFalse(second["consumer_closure_paid"])


if __name__ == "__main__":
    unittest.main()
