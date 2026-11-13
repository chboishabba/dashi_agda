from pathlib import Path
import sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import cybersyn_nvidia_sec_maturity_ladder_20261113 as m

class NvidiaSECCommitmentsTests(unittest.TestCase):
 def test_reported_totals_and_component_reconciliation(self):
  r=m.compute()
  self.assertEqual(r["main_scheduled_total_usd_bn"],366)
  self.assertEqual(r["additional_commitments_total_usd_bn"],56)
  self.assertEqual(r["main_first_three_fiscal_years_usd_bn"],318)
 def test_schedule_has_fiscal_year_shape(self):
  r=m.compute()
  self.assertEqual(len(r["ledger"]),12)
  self.assertEqual(r["ledger"][0]["fiscal_year"],"FY2027_remainder")
  self.assertEqual(r["ledger"][0]["components_total_usd_bn"],120)
 def test_ohio_guarantee_is_delayed_contingent_cap(self):
  r=m.compute()
  self.assertEqual(r["Ohio_guarantee_max_usd_bn"],105)
  self.assertEqual(r["Ohio_guarantee_earliest_first_phase_expected"],"FY2029")
  self.assertFalse(r["empirical_loss_realisation_proven"])
 def test_no_semantic_total_promotion(self):
  r=m.compute()
  self.assertIn("Do not add",r["warning"])
  self.assertFalse(r["kernel_certified"])
if __name__=="__main__":
 unittest.main()
