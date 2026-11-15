#!/usr/bin/env python3
import unittest
from ksw668_f8_normal_operator_comparison import diagnostics
class NormalSchemeComparison(unittest.TestCase):
 def setUp(self):
  self.rows=[dict(retarded_TT_yy_scaled_by_eps4=1.,receiver_intrinsic_4D_electric_Weyl=2.,
    receiver_projected_5D_electric_Weyl=3.,far_TT_yy_scaled_by_eps4=.1,
    far_intrinsic_4D_electric_Weyl=.01,far_projected_5D_electric_Weyl=.03),
   dict(retarded_TT_yy_scaled_by_eps4=2.,receiver_intrinsic_4D_electric_Weyl=4.,
    receiver_projected_5D_electric_Weyl=6.,far_TT_yy_scaled_by_eps4=.2,
    far_intrinsic_4D_electric_Weyl=.02,far_projected_5D_electric_Weyl=.06)]
 def test_two_grid_warning(self):self.assertTrue(diagnostics(self.rows)['only_two_grids'])
 def test_both_weyl_open(self):self.assertFalse(diagnostics(self.rows)['receiver_both_Weyl_convergence_accepted'])
 def test_drift(self):self.assertEqual(diagnostics(self.rows)['retarded_TT_yy_scaled_by_eps4']['relative_drift_vs_medium'],.5)
 def test_outside_ratio(self):self.assertAlmostEqual(diagnostics(self.rows)['receiver_projected_5D_electric_Weyl']['far_to_receiver_medium'],.01)
 def test_no_observation(self):self.assertFalse(diagnostics(self.rows)['empirical_graviton_observed'])
if __name__=='__main__':unittest.main(verbosity=2)
