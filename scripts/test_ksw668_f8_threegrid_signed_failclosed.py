import unittest
from ksw668_f8_threegrid_signed_failclosed import verify,GRID
class OriginalThreeGridSignedWeylAudit(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.d=verify()
 def test_three_grids_completed(self):self.assertEqual(len(self.d['grids']),3)
 def test_original_compact_source(self):self.assertEqual(self.d['source'].count('eps=.04'),1)
 def test_original_twelve_receiver(self):self.assertEqual(self.d['Poincare_receiver_t'],12)
 def test_three_harmonic_digits(self):self.assertEqual(self.d['native_Base369_unsigned_channel_index'],[0,1,2])
 def test_three_physical_dimensions(self):self.assertEqual(self.d['radial_effective_dimensions'],[3,7,11])
 def test_causal_radial_wall_exclusion(self):
  d=self.d['finite_box'];self.assertGreater(d['radial_oneway_min_from_source'],d['source_to_receiver_available_Poincare_span'])
 def test_causal_normal_reflection_exclusion(self):
  d=self.d['finite_box'];self.assertGreater(d['normal_boundary_reflected_path_lower_bound'],d['source_to_receiver_available_Poincare_span'])
 def test_fine_grid_available(self):self.assertEqual(GRID['fine'],(.006,.009,.0012))
 def test_three_E4_independent_mode_drift_grows(self):
  self.assertTrue(all(abs(x['fine_minus_medium'])>abs(x['medium_minus_coarse']) for x in self.d['per_harmonic_signed_spatial_refinement']['E4']))
 def test_three_E5_independent_mode_drift_grows(self):
  self.assertTrue(all(abs(x['fine_minus_medium'])>abs(x['medium_minus_coarse']) for x in self.d['per_harmonic_signed_spatial_refinement']['E5']))
 def test_ell0_large_E4(self):
  self.assertGreater(self.d['per_harmonic_signed_spatial_refinement']['E4'][0]['ratio_abs_successive_changes'],9)
 def test_temporal_readout_not_main_factor(self):
  x=self.d['per_harmonic_signed_spatial_refinement']['E4'][0]
  self.assertGreater(abs(x['fine_minus_medium'])/abs(x['fine_time_readout_disagreement']),1000)
 def test_fine_timestep_half_not_accepted(self):self.assertIn('TIMED OUT',self.d['temporal_separation']['fine_dt_halved_attempt'])
 def test_physical_Weyl_still_open(self):self.assertFalse(self.d['closure']['three_grid_original_E4_E5_acceptance'])
if __name__=='__main__':unittest.main()
