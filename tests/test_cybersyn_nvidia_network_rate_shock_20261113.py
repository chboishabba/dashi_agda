"""Deterministic numerical regression for November 2026 NVIDIA/energy/rates scenarios."""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import cybersyn_nvidia_network_rate_shock_20261113 as m

class NvidiaNetworkRateCutTests(unittest.TestCase):
    def test_grid_cardinality_and_boundaries(self):
        r=m.compute()
        self.assertEqual(len(r["cases"]),576)
        self.assertEqual(len(r["rate_cases"]),12)
        self.assertFalse(r["empirically_calibrated"])
        self.assertFalse(r["JMD_builder_integrated"])
        self.assertFalse(r["Agda_kernel_accepted"])

    def test_au_domestic_and_imports_conserve(self):
        for row in m.compute()["cases"]:
            self.assertAlmostEqual(row["AU_investment_delayed_aud_bn"],
                row["AU_domestic_spend_delayed_aud_bn"] +
                row["AU_imports_delayed_aud_bn"],places=6)

    def test_network_cost_is_only_hypothetical_upper_envelope(self):
        for row in m.compute()["cases"]:
            self.assertGreaterEqual(row["hypo_Ausgrid_DC_component_aud_m"],
                                    row["hypo_household_network_incidence_aud_m"])
            self.assertLessEqual(row["hypo_Ausgrid_DC_component_aud_m"],353)

    def test_nvidia_exposures_are_not_added_or_realised(self):
        r=m.compute()
        self.assertEqual(r["optional_backstop_reduction_usd_bn"]["25pct"],31.25)
        self.assertEqual(r["current_actual_cancelled_AU_pipeline"],"not measured")

    def test_central_bank_rule_is_conditional(self):
        rows=m.compute()["rate_cases"]
        baseline=next(x for x in rows if x["assumed_underlying_inflation_shock_pp"]==0 and
                      x["assumed_output_gap_shock_pp"]==0)
        self.assertAlmostEqual(baseline["rba_hypo_rate_pct"],4.85)
        self.assertAlmostEqual(baseline["fed_hypo_midpoint_pct"],3.875)
        self.assertAlmostEqual(baseline["hypo_policy_rule_change_bp"],0)
if __name__=="__main__":
    unittest.main()
