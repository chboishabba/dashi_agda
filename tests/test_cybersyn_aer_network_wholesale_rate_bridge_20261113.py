from pathlib import Path
import sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import cybersyn_aer_network_wholesale_rate_bridge_20261113 as m
class AERCostStackTests(unittest.TestCase):
 def test_actual_benchmark_components(self):
  r=m.compute()
  self.assertEqual(r["year_on_year_cost_stack_aud"]["network"],66.31)
  self.assertAlmostEqual(r["year_on_year_cost_stack_aud"]["wholesale"],-100.18)
  self.assertEqual(r["published_total_change_aud"],-66)
 def test_no_false_data_centre_attribution(self):
  r=m.compute()
  self.assertEqual(r["data_centre_cost_causal_share"],"unidentified")
  self.assertFalse(r["empirical_CPI_pass_through_estimated"])
  self.assertFalse(r["monetary_rate_rule_estimated"])
 def test_cpi_assumptions_explicit_and_signed(self):
  r=m.compute()
  self.assertEqual(len(r["incidence"]),18)
  for row in r["incidence"]:
   if row["cost_case"]=="all_cost_components":
    self.assertLess(row["hypothetical_CPI_contribution_pp"],0)
   else:
    self.assertGreater(row["hypothetical_CPI_contribution_pp"],0)
 def test_distinct_aer_and_ausgrid_customer_profiles(self):
  r=m.compute()
  self.assertEqual(r["AER_average_4044kWh_flat_network_increase_aud"],63.81)
  self.assertEqual(r["Ausgrid_illustrative_5MWh_network_increase_aud"],73.81)
if __name__=="__main__":
 unittest.main()
