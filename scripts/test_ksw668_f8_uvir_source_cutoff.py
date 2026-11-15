#!/usr/bin/env python3
import unittest
import math
import numpy as np
from ksw668_f8_uvir_source_cutoff import audit,crosscheck,source_transform
class OriginalUVIR(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.a=crosscheck()
 def test_zero_mode(self):self.assertAlmostEqual(source_transform([0.])[0],1)
 def test_fourier_charfunc_bound(self):self.assertTrue(np.all(abs(source_transform(np.arange(0,100,2)))<=1+1e-11))
 def test_IR_TT(self):self.assertEqual(self.a['moments']['10']['IR_exponent'],11)
 def test_IR_six_derivatives(self):self.assertEqual(self.a['moments']['14']['IR_exponent'],15)
 def test_exact_original_cutoff(self):self.assertAlmostEqual(self.a['grid_scaled_k_cutoffs'][-1],.024*math.pi*768/4)
 def test_monotonic_cutoffs(self):
  for p in ('10','14'):
   a=self.a['moments'][p]['captured_fraction_UPPER_BOUND_vs_full']
   self.assertTrue(a[0]<a[1]<a[2])
 def test_TT_UV_cutoff_failure(self):self.assertLess(self.a['moments']['10']['captured_fraction_UPPER_BOUND_vs_full'][-1],.012)
 def test_six_deriv_UV_cutoff_failure(self):self.assertLess(self.a['moments']['14']['captured_fraction_UPPER_BOUND_vs_full'][-1],2e-5)
 def test_quadrature_agreement(self):self.assertLess(max(self.a['radial_quadrature_crosscheck_max_abs_drift'].values()),1e-7)
 def test_shells_positive_and_sum_one(self):
  for p in ('10','14'):
   arr=[x['reference_fraction'] for x in self.a['moments'][p]['dyadic_reference_shells']]
   self.assertTrue(all(x>=0 for x in arr));self.assertAlmostEqual(sum(arr),1,places=9)
 def test_no_receiver_promotion(self):
  self.assertFalse(self.a['Weyl_receiver_convergence_certified'])
  self.assertFalse(self.a['source_spectral_cutoff_acceptance'])
 def test_negative_domain(self):
  with self.assertRaises(ValueError):audit(eps=-.1)
 def test_finite_grid_not_Agda(self):self.assertFalse(self.a['Agda_pinned_kernel_verified'])
if __name__=='__main__':unittest.main(verbosity=2)
