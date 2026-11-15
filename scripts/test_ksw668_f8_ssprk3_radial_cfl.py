#!/usr/bin/env python3
import unittest
from ksw668_f8_ssprk3_radial_cfl import (
 symbolic,fv_matrix,spectral,mode_energy_growth,audit)
class RadialSSPRK3(unittest.TestCase):
 def test_symbolic_modulus(self):self.assertIn('x^4',symbolic()['modulus_square_minus_one'])
 def test_weighted_fv_d3(self):self.assertEqual(fv_matrix(3,10)[1].shape,(10,10))
 def test_weighted_fv_d7(self):self.assertEqual(fv_matrix(7,10)[1].shape,(10,10))
 def test_weighted_fv_d11(self):self.assertEqual(fv_matrix(11,10)[1].shape,(10,10))
 def test_at_imaginary_boundary(self):self.assertAlmostEqual(mode_energy_growth(3,1),1)
 def test_above_boundary(self):self.assertGreater(mode_energy_growth(4,1),1)
 def test_below_boundary(self):self.assertLess(mode_energy_growth(2,1),1)
 def test_gershgorin(self):
  for d in (3,7,11):
   s=spectral(d);self.assertLess(s['lambda_max'],s['gershgorin_upper_bound'])
 def test_original_eleven_cfl(self):self.assertLess(spectral(11)['sufficient_dt_over_dr'],.27)
 def test_bad_prior_dt(self):self.assertGreater(audit()['radial_11d_045_one_step_energy_growth'],1.8)
 def test_safe_radial_dt(self):
  s=spectral(11)
  self.assertLessEqual(mode_energy_growth(s['lambda_max'],.24*.01),1+1e-14)
 def test_invalid_dimension(self):
  with self.assertRaises(ValueError):fv_matrix(5)
 def test_no_full_CFL_promotion(self):self.assertFalse(audit()['original_full_moving_Israel_SSPRK3_CFL_accepted'])
if __name__=='__main__':unittest.main(verbosity=2)
