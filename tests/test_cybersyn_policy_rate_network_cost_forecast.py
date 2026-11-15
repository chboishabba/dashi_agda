"""Rate source identity and exact scenario conservation / no-promotions."""
import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import cybersyn_policy_rate_network_cost_forecast as mod

class PolicyRateNetworkTest(unittest.TestCase):
    def test_fed_distribution_normalises(self):
        for d in mod.FED_MIDPOINT_DISTRIBUTIONS.values():
            self.assertAlmostEqual(sum(d.values()),100)
    def test_fed_dec_hike_market(self):
        r=mod.calculate()
        self.assertAlmostEqual(r["fed_market_implied"][0]["implied_expected_target_midpoint_pct"],4.15475,places=4)
    def test_rba_overnight_not_target(self):
        self.assertEqual(mod.RBA_ASX_YIELDS["2026-12"],4.855)
    def test_ausgrid_regulated_components_rounding(self):
        r=mod.calculate()
        self.assertEqual(r["ausgrid_allowance_change_aud_m"],353)
        self.assertEqual(sum(r["ausgrid_rounded_revenue_components_aud_m"].values()),354)
    def test_debt_interest_arithmetic(self):
        r=mod.calculate()
        self.assertIn(2.5,[v["hypothetical_interest_increase_aud_m_year"] for v in r["illustrative_network_debt_rate_sensitivity"]])
    def test_non_promotions(self):
        r=mod.calculate()
        self.assertFalse(r["real_world_marginal_cost_causality_established"])
        self.assertFalse(r["independent_policy_rate_forecast_validated"])
        self.assertFalse(r["kernel_proof_accepted"])

if __name__=="__main__":unittest.main()
