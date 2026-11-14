"""Non-promoting, data-free regression tests for the Ibrahim FLN reference census."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import ibrahim_fln_reference_analysis as ref  # noqa: E402


class IbrahimFLNReferenceTests(unittest.TestCase):
    def test_seven_node_historical_fixture_as_graph_only(self) -> None:
        # Seven-node source-attributed core in
        # IbrahimFirstLinkPhilosophyCoreBasinDeweyQidExact.agda.
        cycle = {
            "Awareness": "Conscious",
            "Conscious": "Consciousness",
            "Consciousness": "Quality (philosophy)",
            "Quality (philosophy)": "Philosophy",
            "Philosophy": "Reality",
            "Reality": "Existence",
            "Existence": "Awareness",
        }
        result = ref.summarise(cycle, top=7)
        self.assertEqual(result["article_count"], 7)
        self.assertEqual(result["cycle_count"], 1)
        self.assertEqual(result["basins"][0]["starting_articles"], 7)
        self.assertEqual(result["basins"][0]["exact_share"], "7/7")
        self.assertTrue(all(x["distinct_starts_visiting"] == 7
                            for x in result["top_single_visit_funnels"]))
        self.assertFalse(result["historical_traversal_funnel_algorithm_parity_paid"])

    def test_published_traversal_visits_and_funnel_figure(self) -> None:
        # Exact graph drawn in the Ibrahim-Danforth-Dodds 2016 draft
        # (Figure 2 traversal visits; Figures 3-4 traversal funnels).
        graph = {
            "A": "B", "B": "C", "C": "A",
            "D": "C", "E": "C", "F": "E", "G": "E",
        }
        terminals, basins = ref.terminal_census(graph)
        visits = ref.paper_traversal_visits(graph, terminals, basins)
        published = ref.traversal_funnels(
            graph, terminals, basins, include_cycle_entry=True
        )
        old_pseudocode = ref.traversal_funnels(
            graph, terminals, basins, include_cycle_entry=False
        )
        self.assertEqual(visits, {
            "A": 7, "B": 7, "C": 7,
            "D": 0, "E": 2, "F": 0, "G": 0,
        })
        self.assertEqual(published, {
            "A": 0, "B": 0, "C": 4,
            "D": 0, "E": 2, "F": 0, "G": 0,
        })
        self.assertEqual(old_pseudocode["C"], 0)
        self.assertEqual(old_pseudocode["E"], 2)

    def test_incoming_tree_and_cycle_distinct_start_counts(self) -> None:
        graph = {"a": "b", "b": "c", "c": "d", "d": "c", "e": "b"}
        terminals, basins = ref.terminal_census(graph)
        flows = ref.single_visit_funnels(graph, terminals, basins)
        self.assertEqual(flows, {"a": 1, "b": 3, "c": 5, "d": 5, "e": 1})
        self.assertEqual(set(terminals.values()), {("cycle", ("c", "d"))})

    def test_missing_target_is_not_conflated_with_dead_end(self) -> None:
        graph = {"a": "not_in_dump", "b": None, "c": "c"}
        result = ref.summarise(graph, top=4)
        self.assertEqual(result["unresolved_target_count"], 1)
        self.assertEqual(result["dead_end_count"], 1)
        self.assertEqual(result["cycle_count"], 1)
        self.assertEqual(sum(x["starting_articles"] for x in result["basins"]), 3)

    def test_edit_impact_bound_and_unchanged_component(self) -> None:
        old = {"a": "b", "b": "c", "c": "c", "z": "z", "w": "z"}
        new = {"a": "b", "b": "z", "c": "c", "z": "z", "w": "z"}
        result = ref.compare_same_carrier(old, new)
        self.assertEqual(result["edge_changes"], 1)
        self.assertEqual(result["old_reverse_reachable_bound"], 2)
        self.assertEqual(result["actually_changed_terminal_outcomes"], 2)
        self.assertTrue(result["outside_bound_unaffected"])

    def test_bounded_edit_can_leave_terminal_cycle_unchanged(self) -> None:
        old = {"a": "b", "b": "c", "c": "b", "z": "z"}
        new = {"a": "c", "b": "c", "c": "b", "z": "z"}
        result = ref.compare_same_carrier(old, new)
        self.assertEqual(result["edge_changes"], 1)
        self.assertEqual(result["actually_changed_terminal_outcomes"], 0)

    def test_different_carrier_cannot_be_compared_without_transport(self) -> None:
        with self.assertRaisesRegex(ValueError, "typed identity-transport"):
            ref.compare_same_carrier({"a": "a"}, {"b": "b"})

    def test_manifest_hash_and_nonpromotion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "fixture.json"
            source.write_text(json.dumps({"a": "a"}), encoding="utf-8")
            manifest = root / "manifest.json"
            fields = {
                "source_author": "DASHI synthetic fixture",
                "source_title": "One-node reflexive graph",
                "canonical_url": "fixture:unit-test",
                "source_role": "synthetic test input, not primary source",
                "version_or_revision": "fixture-v1",
                "parser_policy": "explicit first-link mapping",
                "link_selection_policy": "already selected by fixture",
                "expected_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "claim_scope": "unit test only",
                "qid_status": "not-applicable",
                "dewey_status": "not-applicable",
            }
            manifest.write_text(json.dumps(fields), encoding="utf-8")
            checked = ref.check_manifest(manifest, source)
            self.assertEqual(checked["verified_local_graph_sha256"],
                             fields["expected_sha256"])
            fields["expected_sha256"] = "0" * 64
            manifest.write_text(json.dumps(fields), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                ref.check_manifest(manifest, source)


if __name__ == "__main__":
    unittest.main()
