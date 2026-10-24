"""Synthetic source-contract checks for temporal motif evaluator, no Erowid data."""
import copy
import unittest
from scripts.evaluate_dmt_temporal_motifs import validate, evaluate


def fixture():
    return {"schema": "dashi-dmt-temporal-motifs-v1",
            "observation_unit": "report",
            "governance": {
                "written_permission_reference": "synthetic-fixture-only",
                "chronology_method_reference": "manually constructed ordinals"},
            "reports": [
                {"report_id": str(i), "chronology_verified": True,
                 "events": [{"ordinal": j, "motif": x}
                            for j, x in enumerate(seq)]}
                for i, seq in enumerate((
                    ("lattice", "tunnel", "face"),
                    ("lattice", "face", "tunnel"),
                    ("face", "tunnel", "lattice")))]}


class TestTemporalMotifs(unittest.TestCase):
    def test_synthetic(self):
        result = evaluate(fixture())
        self.assertEqual(result["report_count"], 3)
        self.assertEqual(sum(x["transitions"] for x in result["report_results"]), 6)
        self.assertFalse(result["independent_external_agent_inferred"])

    def test_rights_block(self):
        f = fixture()
        f["governance"]["written_permission_reference"] = ""
        with self.assertRaises(ValueError):
            validate(f)

    def test_chronology_block(self):
        f = fixture()
        f["reports"][0]["chronology_verified"] = False
        with self.assertRaises(ValueError):
            validate(f)

    def test_identity_block(self):
        f = fixture()
        f["reports"][1]["report_id"] = f["reports"][0]["report_id"]
        with self.assertRaises(ValueError):
            validate(f)

    def test_order_block(self):
        f = fixture()
        f["reports"][0]["events"][1]["ordinal"] = 0
        with self.assertRaises(ValueError):
            validate(f)

    def test_static_frequency_not_sequence(self):
        f = fixture()
        f["reports"][0].pop("events")
        f["reports"][0]["category_counts"] = {"lattice": 2}
        with self.assertRaises(ValueError):
            validate(f)

    def test_report_permutation_invariance(self):
        f = fixture()
        g = copy.deepcopy(f)
        g["reports"].reverse()
        a = {r["report_id"]: r["likelihood_ratio_exact"]
             for r in evaluate(f)["report_results"]}
        b = {r["report_id"]: r["likelihood_ratio_exact"]
             for r in evaluate(g)["report_results"]}
        self.assertEqual(a, b)


if __name__ == "__main__":
    unittest.main()
