import importlib.util
import json
import unittest
from pathlib import Path
from copy import deepcopy

ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location("ftworld",ROOT/"scripts"/"follow_through_revisable_source_world.py")
mod=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)
WORLD=json.loads((ROOT/"docs/receipts/FollowThroughRevisableSourceWorld20261026.json").read_text())

class RevisableSourceWorldTests(unittest.TestCase):
    def test_sourced_claim_stays_source_reported(self):
        q=mod.report(WORLD)
        self.assertEqual(q["claims"]["reportedDIRank"]["level"],"sourceReported")
        self.assertEqual(q["claims"]["reportedDIRank"]["unpaid"],[])

    def test_missing_does_not_mean_false(self):
        q=mod.report(WORLD)
        self.assertFalse(q["claims"]["rankRobust"]["reproducible_now"])
        self.assertEqual(set(q["claims"]["rankRobust"]["unpaid"]),
                         {"abtExactCells","houseMatchedChanges","stpierreTwoSpecs"})

    def test_no_promotion_after_evidence_receipt(self):
        w=deepcopy(WORLD)
        for e in w["evidence"]:
            if e["id"] in {"abtExactCells","houseMatchedChanges","stpierreTwoSpecs"}:
                e.update(status="present",locator="TEST SYNTHETIC")
        q=mod.report(w)
        self.assertEqual(q["claims"]["rankRobust"]["level"],"unresolved")
        self.assertTrue(q["claims"]["rankRobust"]["reproducible_now"])

    def test_known_absence_scoped(self):
        w=deepcopy(WORLD)
        w["evidence"][0].update(status="knownAbsent")
        with self.assertRaisesRegex(ValueError,"known absent needs scope"): mod.validate(w)

    def test_unsupported_replication_denied(self):
        w=deepcopy(WORLD)
        w["claims"][0]["level"]="independentlyReproduced"
        with self.assertRaisesRegex(ValueError,"unsupported reproduction"): mod.validate(w)

    def test_original_roots_unique(self):
        w=deepcopy(WORLD); w["sources"].append(deepcopy(w["sources"][0]))
        with self.assertRaisesRegex(ValueError,"duplicate roots"): mod.validate(w)

    def test_target_aware_pareto_independent_actions(self):
        q=mod.report(WORLD)
        self.assertIn("acquireAbtTables",{x["action"] for x in q["pareto_frontier"]})
        self.assertIn("acquirePolicyArchives",{x["action"] for x in q["pareto_frontier"]})

    def test_no_mutation_by_hypothetical_actions(self):
        before=json.dumps(WORLD,sort_keys=True)
        mod.report(WORLD)
        self.assertEqual(json.dumps(WORLD,sort_keys=True),before)

    def test_invalid_action_refused(self):
        w=deepcopy(WORLD);w["actions"][0]["targets"].append("fictional")
        with self.assertRaisesRegex(ValueError,"bad target"):mod.report(w)

    def test_every_claim_has_two_sided_discriminator(self):
        q=mod.report(WORLD)
        for claim in q["claims"].values():
            self.assertTrue(claim["severe_test"]["would_narrow"])
            self.assertTrue(claim["severe_test"]["would_strengthen"])
            self.assertEqual(claim["severe_test"]["test_status"],"notRun")

    def test_missing_severe_discriminator_rejected(self):
        w=deepcopy(WORLD)
        w["claims"][0].pop("severe_test")
        with self.assertRaisesRegex(ValueError,"bidirectional severe test"):
            mod.validate(w)

if __name__=="__main__":
    unittest.main()
