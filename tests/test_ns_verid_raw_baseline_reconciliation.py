import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from ns_verid_raw_baseline_reconciliation import reconcile

def fixture():
    return {
        "schema_version":"1.4.0",
        "authority":{"theorem_authority":False,"clay_authority":False,"promoted":False},
        "trajectory_manifest":{"matched_cutoffs":[32,48,64]},
        "holdout_trajectories":["matched-N64"],
        "heldout_validation":{"any_nonvacuous_parameter_set_survives_holdout":False},
        "depletion_currency_comparison":{"heldout_validation":{"any_candidate_currency_passes_sampled_heldout_gate":False}},
        "bounded_turnover_potential":{"heldout_signed_escape_validation":{"any_signed_escape_currency_passes_heldout":False}},
        "compact_gamma_potential":{"heldout_compact_escape_validation":{"any_compact_escape_currency_passes_heldout":False}}
    }

class RawReceiptTests(unittest.TestCase):
    def test_reconcile_no_redundant_probe(self):
        r=reconcile(fixture())
        self.assertEqual(r["canonical_leaf"],"b7IntegratedControl")
        self.assertFalse(r["next_probe_execution_required"])
        self.assertIn("cross_shell_currency",r["completed_probes"])
        self.assertFalse(r["authority"]["analytic_B7"])
    def test_abstain_if_missing_verdict(self):
        x=fixture()
        del x["depletion_currency_comparison"]["heldout_validation"]
        with self.assertRaises(ValueError):
            reconcile(x)
    def test_refuse_promotion(self):
        x=fixture()
        x["authority"]["clay_authority"]=True
        with self.assertRaises(ValueError):
            reconcile(x)
    def test_deterministic(self):
        self.assertEqual(reconcile(fixture()),reconcile(fixture()))

if __name__=="__main__":
    unittest.main()
