#!/usr/bin/env python3
import unittest
from ksw668_f8_exact_spatial_tt_local import symbolic,evaluate,audit
class OriginalExactSpatialTT(unittest.TestCase):
 def test_identity(self):self.assertTrue(symbolic()['symbolic_nontrivial_Gaussian_identity_pass'])
 def test_source_local(self):self.assertTrue(symbolic()['compact_source_local_order4'])
 def test_inside_nonzero(self):self.assertGreater(abs(evaluate()['exact_TT_yy']),1000)
 def test_outside_exact_zero(self):self.assertEqual(evaluate(r=1.822)['exact_TT_yy'],0)
 def test_outside_flag(self):self.assertTrue(evaluate(r=1.822)['outside_source'])
 def test_epsilon_scale(self):
  a=evaluate(eps=.024,r=.008)['exact_TT_yy']
  b=evaluate(eps=.048,r=.016)['exact_TT_yy']
  self.assertAlmostEqual(a/b,8,places=8)
 def test_zero_radius_invalid(self):
  with self.assertRaises(ValueError):evaluate(r=0)
 def test_not_physical_Weyl(self):self.assertFalse(audit()['physical_Weyl_accepted'])
if __name__=='__main__':unittest.main(verbosity=2)
