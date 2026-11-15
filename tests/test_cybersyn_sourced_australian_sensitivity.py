"""Small exact arithmetic tests for sourced Australian sensitivity cut."""
from __future__ import annotations
from decimal import Decimal as D
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import cybersyn_sourced_australian_sensitivity as mod

class SourcedSensitivityTests(unittest.TestCase):
    def test_forecast_multipliers(self):
        r=mod.compute()["diagnostics"]
        self.assertAlmostEqual(r["fy36_over_fy26_demand_multiple"],33.7/5.1)
        self.assertAlmostEqual(r["incremental_fy36_over_fy26_twh"],28.6)
    def test_nextdc_guidance_revisions(self):
        r=mod.compute()["diagnostics"]
        self.assertAlmostEqual(r["nextdc_revenue_midpoint_revision_aud_m"],140.0)
        self.assertAlmostEqual(r["nextdc_ebitda_midpoint_revision_aud_m"],142.5)
    def test_all_energy_rows_conserve(self):
        r=mod.compute()
        self.assertEqual(len(r["energy"]),36)
        for row in r["energy"]:
            self.assertAlmostEqual(row["gross_value_aud_m"],
                row["consumer_incidence_aud_m"]+row["other_incidence_aud_m"])
    def test_guarantees_are_assumptions_not_observed(self):
        r=mod.compute()
        self.assertEqual(len(r["guarantees"]),3)
        for row in r["guarantees"]:
            self.assertAlmostEqual(140,
                row["public_exposure_aud_m"]+row["private_exposure_aud_m"])
    def test_no_empirical_or_proof_promotion(self):
        r=mod.compute()
        self.assertFalse(r["real_data_timeseries_backtest"])
        self.assertFalse(r["empirical_macro_validation_completed"])
        self.assertFalse(r["authoritative_jmd_builder_integrated"])
        self.assertFalse(r["agda_kernel_accepted"])

if __name__=="__main__": unittest.main()
