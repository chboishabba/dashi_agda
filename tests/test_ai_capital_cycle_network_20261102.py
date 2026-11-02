"""Finite regression for the source-written capital-cycle continuation model.

Run: python -m unittest discover -s tests -p 'test_ai_capital_cycle_network_20261102.py'
This verifies executable scenario arithmetic and stops, not future forecasts,
creditor loss ownership, market availability or Agda kernel proof.
"""
import pathlib
import runpy
import unittest

ROOT=pathlib.Path(__file__).resolve().parents[1]
SCRIPT=ROOT / "scripts/ai_capital_cycle_network_20261102.py"
AGDA=ROOT / "DASHI/Governance/AIContinuingCapitalFundingMaxCut20261102Exact.agda"
ATLAS=ROOT / "DASHI/Governance/KnowledgeProcessingCaptureSourceAtlas20261101Exact.agda"
AGGREGATE=ROOT / "DASHI/Governance/Everything.agda"
ROADMAP=ROOT / "Docs/AIContinuingCapitalFundingMaxCut20261102.md"

class CapitalCycleMaxCut(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ns=runpy.run_path(str(SCRIPT),run_name="_import_only_")
        cls.out=cls.ns["check"]()

    def test_baseline_and_compound_borrowing(self):
        x=self.out
        self.assertAlmostEqual(x["old_envelope"]["peak_cash_gap"],120.730,places=2)
        self.assertAlmostEqual(x["new_12pct_coupon"]["peak_cash_gap"],152.994,places=2)
        self.assertAlmostEqual(x["lag_and_extra_refresh"]["peak_cash_gap"],250.725,places=2)
        self.assertAlmostEqual(x["expensive_capital_and_rollover"]["peak_cash_gap"],282.413,places=2)

    def test_synthetic_credit_supply_rejects_invalid_growth_path(self):
        for label,year in (("capital_limit_10bn",2027),("capital_limit_20bn",2028)):
            with self.subTest(label=label):
                r=self.out[label]
                self.assertEqual(r["first_failed_financing_year"],year)
                self.assertFalse(r["fully_financed_hypothetical_growth"])
                self.assertEqual(r["yearly"][-1]["year"],year)
        self.assertGreater(self.out["capital_limit_20bn"]["unfunded_amount_first_failure"],8)

    def test_gross_rollover_does_not_duplicate_investment(self):
        r=self.out["expensive_capital_and_rollover"]
        self.assertAlmostEqual(r["gross_issuance_with_hypothetical_2027_roll"]-
                               r["total_new_money_drawn"],6.052,places=2)

    def test_prepaid_cash_sensitivity_is_not_a_claim_of_fake_revenue(self):
        self.assertGreater(self.out["normalize_advance_cashflow"]["peak_cash_gap"],
                           self.out["new_12pct_coupon"]["peak_cash_gap"])
        self.assertTrue(self.out["normalize_advance_cashflow"]["fully_financed_hypothetical_growth"])

    def test_guarantee_is_conditional_not_automatic_debt(self):
        f=self.ns["project_loss_allocation"]
        self.assertEqual(f(15,10.5,5,False)["lender_loss_after_sponsor"],4.5)
        self.assertEqual(f(15,10.5,5,True)["sponsor_contingent_payment"],4.5)

    def test_source_owners_and_aggregator(self):
        source=AGDA.read_text(encoding="utf-8")
        for owner in ("AIInfrastructureConsumerIndexedFibreAdequacyExact",
                      "AIInfrastructureConsumerFibreRefinementSchedulerExact",
                      "GlobalFundingLiquidityRealisationExact",
                      "AIOffBalanceCapitalRecovery20261101Exact",
                      "currentMaturityCannotDetermineFutureBuild",
                      "h1OperatingCashWorkingCapitalIdentity"):
            self.assertIn(owner,source)
        self.assertNotIn("postulate ",source)
        self.assertEqual(AGGREGATE.read_text().count(
            "import DASHI.Governance.AIContinuingCapitalFundingMaxCut20261102Exact"),1)
        self.assertIn("coreWeaveH1SecCashClock",ATLAS.read_text())
        self.assertIn("capital_limit_20bn",SCRIPT.read_text())
        self.assertIn("Original observations",ROADMAP.read_text())

if __name__=="__main__":
    unittest.main()
