#!/usr/bin/env python3
import unittest
from ksw668_f8_static_tt_reconstruction_null import reconstruct,audit
class CompactStaticNull(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.a=audit()
 def test_exact_zero(self):self.assertTrue(all(x['exact_local_compact_TT_yy_outside_support']==0 for x in self.a['results']))
 def test_same_3D_angular(self):self.assertTrue(reconstruct()['original_F8_angular_Bessel_rule'])
 def test_outside_original_source(self):self.assertGreater(reconstruct()['r'],50*reconstruct()['eps'])
 def test_grid256_false_positive(self):self.assertGreater(self.a['results'][0]['absolute_static_reconstruction_error'],100)
 def test_grid512_false_positive(self):self.assertGreater(self.a['results'][1]['absolute_static_reconstruction_error'],100)
 def test_grid768_false_positive(self):self.assertGreater(self.a['results'][2]['absolute_static_reconstruction_error'],100)
 def test_legendre_quadrature_independent(self):self.assertLess(self.a['radial_quadrature_96_vs_384_difference'],1e-7)
 def test_no_receiver_convergence(self):self.assertFalse(self.a['full_3D_F8_receiver_accepted'])
 def test_wrong_support_rejected(self):
  with self.assertRaises(ValueError):reconstruct(r=.01)
 def test_not_wave_PDE(self):self.assertFalse(reconstruct()['original_moving_retarded_PDE_tested'])
if __name__=='__main__':unittest.main(verbosity=2)
