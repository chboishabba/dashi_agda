#!/usr/bin/env python3
import unittest
from ksw668_f8_ternary_channel_drift import inspect
class TernaryChannelSignedErrorBudget(unittest.TestCase):
 def setUp(self):
  def row(H,E4,E5):
   return dict(intrinsic_4D_weyl_spatial_operator='full_reconstructed_Delta3',raw_mode_values=H,
     retarded_TT_yy_scaled_by_eps4=sum(H),far_mode_values=[.1,.2,.3],
     receiver_mode_intrinsic_4D_electric_Weyl=E4,
     receiver_intrinsic_4D_electric_Weyl=sum(E4),
     far_mode_intrinsic_4D_electric_Weyl=[.01,.02,.03],
     receiver_mode_projected_5D_electric_Weyl=E5,
     receiver_projected_5D_electric_Weyl=sum(E5),
     far_mode_projected_5D_electric_Weyl=[.001,.002,.003])
  self.sample=inspect([row([2.,-1.,3.],[1.,-2.,4.],[2.,-3.,4.]),
                       row([5.,-2.,3.],[5.,-5.,4.],[5.,-4.,4.])])
 def test_three_channels(self):self.assertEqual([x['ell'] for x in self.sample['actual_numerical_data']['E4']['mode_drift']],[0,2,4])
 def test_ternary_index(self):self.assertEqual(self.sample['ternary_index'],[0,1,2])
 def test_signed_error_cancellation(self):self.assertGreater(self.sample['actual_numerical_data']['E4']['cancellation_ratio'],1)
 def test_triangle_error(self):
  for x in self.sample['actual_numerical_data'].values():
   self.assertLessEqual(abs(x['aggregate_drift']),x['absolute_channel_drift_sum']+1e-12)
 def test_not_physical_symmetry(self):self.assertFalse(self.sample['physical_369_rotation_claimed'])
 def test_fail_closed_two_grid(self):self.assertFalse(self.sample['both_Weyl_convergence_certified'])
 def test_wrong_grid_count(self):
  with self.assertRaises(ValueError):inspect([])
if __name__=='__main__':unittest.main(verbosity=2)
