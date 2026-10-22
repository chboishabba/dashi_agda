import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from ns_verid_abcd_bidi_replay import choose

class ReplayTests(unittest.TestCase):
    def test_falsified_move_rejected(self):
        report=choose()
        self.assertEqual(report["canonical_leaf"],"b7IntegratedControl")
        self.assertEqual(report["selected_next_experiment"],"cross_shell_coherence")
        self.assertFalse(report["candidate_portfolio"][0]["admissible"])
        self.assertFalse(any(report["promotion"].values()))

    def test_reproducible(self):
        self.assertEqual(choose(),choose())

    def test_requires_negative_evidence(self):
        with self.assertRaises(ValueError):
            choose({"0.01": 0.01})

if __name__=="__main__":
    unittest.main()
