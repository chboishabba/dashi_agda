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
        self.assertFalse(q["claims"]["rankRobust"]["prerequisites_located"])
        self.assertEqual(set(q["claims"]["rankRobust"]["unpaid"]),
                         {"abtExactCells","houseMatchedChanges","stpierreTwoSpecs"})

    def test_no_promotion_after_evidence_receipt(self):
        w=deepcopy(WORLD)
        for e in w["evidence"]:
            if e["id"] in {"abtExactCells","houseMatchedChanges","stpierreTwoSpecs"}:
                e.update(status="present",locator="TEST SYNTHETIC")
        q=mod.report(w)
        self.assertEqual(q["claims"]["rankRobust"]["level"],"unresolved")
        self.assertTrue(q["claims"]["rankRobust"]["prerequisites_located"])

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

    def test_causal_evidence_not_paid_by_abt_tables_only(self):
        w=deepcopy(WORLD)
        for e in w["evidence"]:
            if e["id"] in {"abtExactCells","policyOriginal"}:
                e.update(status="present",locator="SYNTHETIC TEST ONLY")
        q=mod.report(w)
        self.assertIn("mediationDesignEvidence",q["claims"]["affectiveMediation"]["unpaid"])
        self.assertIn("nationalExposureAndOutcome",q["claims"]["nationalDecline"]["unpaid"])
        self.assertNotIn("reproducible_now",q["claims"]["reportedDIRank"])

    def test_original_policy_root_not_abt(self):
        self.assertEqual(next(x for x in WORLD["evidence"] if x["id"]=="policyOriginal")["root"],"federalPolicy")

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

    def test_source_roots_not_counted_as_carriers(self):
        w=deepcopy(WORLD)
        w["claims"][0]["supports"]=["apmEpisode","apmEpisode"]
        q=mod.report(w)
        self.assertEqual(q["claims"]["reportedDIRank"]["independent_root_count"],1)
        self.assertEqual(q["claims"]["reportedDIRank"]["source_roots"],["apm2026"])

    def test_policy_and_outcome_different_roots(self):
        by_id={e["id"]:e["root"] for e in WORLD["evidence"]}
        self.assertNotEqual(by_id["policyOriginal"],by_id["abtExactCells"])

if __name__=="__main__":
    unittest.main()
