import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from ns_abcd_current_frontier_reconciliation import reconcile,ROOT

class CurrentFrontierTests(unittest.TestCase):
    def test_canonical_frontier(self):
        r=reconcile()
        self.assertFalse(r["reconciliation"]["R832_concrete_vector_evaluation_closed"])
        self.assertFalse(r["reconciliation"]["R832_real_ODE_transport_closed"])
        self.assertFalse(r["reconciliation"]["Clay_proof_verified_by_this_audit"])
        self.assertIn("R823-R832",r["reconciliation"]["preferred_periodic_B"])
    def test_missing_source_rejected(self):
        with self.assertRaises(FileNotFoundError):
            reconcile(ROOT/"does-not-exist")

if __name__=="__main__":
    unittest.main()
