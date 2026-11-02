"""DDTL3 legal ordering / original source boundary regression.

This checks a source-written small Python contract model; it does NOT
establish real lender transactions, real CRR compliance, a payout, or that
the Agda module was kernel-accepted.
"""
import pathlib
import runpy
import unittest
from decimal import Decimal as D

ROOT=pathlib.Path(__file__).resolve().parents[1]
PY=ROOT/"scripts/ai_ddtl3_contract_waterfall_20261102.py"
AGDA=ROOT/"DASHI/Governance/AIDDTL3WaterfallAndSameObjectCut20261102Exact.agda"
ATLAS=ROOT/"DASHI/Governance/KnowledgeProcessingCaptureSourceAtlas20261101Exact.agda"
GOV=ROOT/"DASHI/Governance/Everything.agda"

class DDTL3WaterfallRegression(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ns=runpy.run_path(str(PY),run_name="test_import")
        cls.fixture=cls.ns["compare_synthetic_worlds"]()
        cls.receipts=cls.ns["Receipts"]
        cls.claims=cls.ns["Claims"]
        cls.flow=cls.ns["waterfall"]
        cls.crr=cls.ns["crr"]
        cls.stages=cls.ns["STAGES"]

    def test_eight_stage_source_priority(self):
        self.assertEqual(len(self.stages),8)
        self.assertEqual(self.stages[0],"first_eligible_opex")
        self.assertEqual(self.stages[4],"fifth_principal_and_swap_termination")
        self.assertEqual(self.stages[-1],"eighth_distribution_reserve")

    def test_monthly_op_exp_first_priority_cap(self):
        z=self.flow(self.receipts(D(150),D(0),D(0)),
          self.claims(D(70),D(0),D(0),D(0),D(0),D(0),D(0)))
        self.assertEqual(z["stages"][self.stages[0]],D(50))
        self.assertEqual(z["distribution_reserve"],D(100))

    def test_realised_cash_vs_equity_cure_nonidentification(self):
        self.assertEqual(self.crr(85,0,100),self.crr(80,5,100))
        self.assertEqual(self.crr(85,0,100),D(".85"))
        self.assertTrue(self.fixture["same_waterfall_different_terminal_cash"])

    def test_cash_conservation_partial_payment_priority(self):
        z=self.flow(self.receipts(D(10),D(0),D(0)),
          self.claims(D(3),D(2),D(20),D(0),D(4),D(0),D(0)))
        self.assertEqual(z["stages"][self.stages[0]],D(3))
        self.assertEqual(z["stages"][self.stages[1]],D(2))
        self.assertEqual(z["stages"][self.stages[2]],D(5))
        self.assertEqual(z["stages"][self.stages[4]],D(0))
        self.assertEqual(sum(z["stages"].values(),D(0)),D(10))

    def test_cash_trap_and_conditional_reserve_release(self):
        self.assertEqual(self.fixture["with_cash_trap_reserve"],"13")
        self.assertEqual(self.fixture["without_cash_trap_reserve"],"43")
        self.assertFalse(self.fixture["automatic_distribution_proved"])
        z=self.flow(self.receipts(D(85),D(0),D(0)),
          self.claims(D(0),D(0),D(0),D(0),D(0),D(0),D(0),
                      False,False,True))
        self.assertEqual(z["conditional_eligible_release_ceiling"],D(85))
        self.assertFalse(z["actual_company_dividend_observed"])

    def test_hedged_rate_exposure_is_only_a_conditional_subset(self):
        f=self.ns["floating_rate_basis_stress_assuming_effective_hedge"]
        # Assumed full $2.6bn draw (not actual), +400bp parallel rate shock.
        # Fully effective 75% hedge: $26m vs $104m without hedge.
        self.assertEqual(f(2.6,.04,.75,1),D(".026"))
        self.assertEqual(f(2.6,.04,0,1),D(".104"))
        self.assertEqual(f(2.6,.04,.75,0),D(".104"))
        with self.assertRaises(ValueError):
            f(2.6,.04,1.1,1)

    def test_source_priors_and_aggregate(self):
        a=AGDA.read_text()
        atlas=ATLAS.read_text()
        gov=GOV.read_text()
        for v in ("sameAccountAndRatioCannotDetermineTerminalCash",
                  "originalWaterfall","originalCure","firstStepMonthlyOperatingExpenseCapMillionUSD",
                  "reusedFutureBuildFinancingBoundary"):
            self.assertIn(v,a)
        for v in ("coreWeaveDDTL3Sec220WaterfallOriginal","coreWeaveDDTL3CureDecember31Original"):
            self.assertIn(v,atlas)
        self.assertEqual(gov.count("import DASHI.Governance.AIDDTL3WaterfallAndSameObjectCut20261102Exact"),1)
        self.assertNotIn("postulate ",a)

if __name__ == "__main__":
    unittest.main()
