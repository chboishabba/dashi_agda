#!/usr/bin/env python3
import unittest
import numpy as np
from ksw668_f8_radial_sobolev_hierarchy import check,audit,radial_A_power,source_A_power
from ksw668_f8_full_coupled_weighted_sbp_energy import setup
class OriginalRadialSobolevHierarchy(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=audit()
 def test_two_weak_SAT_modes(self):self.assertEqual({x['mode'] for x in self.data['cases']},{3,4})
 def test_original_time_slices(self):self.assertEqual({x['original_t'] for x in self.data['cases']},{1.,4/3,2.,12.})
 def test_original_3D_TT_multipoles(self):self.assertTrue(all(x['exact_TT_angular_modes']==[0,2,4] for x in self.data['cases']))
 def test_all_four_powers(self):self.assertTrue(all(x['finite_radial_sobolev_orders']==[0,1,2,3] for x in self.data['cases']))
 def test_commutation_actual_Numba_sourced_stage(self):
  self.assertLess(max(y['commutation_relative_error'] for a in self.data['cases'] for y in a['rows']),1e-10)
 def test_actual_compact_modal_source(self):self.assertTrue(self.data['original_compact_3D_TT_source'])
 def test_energy_nonnegative_high_orders(self):self.assertTrue(all(y['higher_radial_energy']>=0 for a in self.data['cases'] for y in a['rows']))
 def test_high_source_norm_not_uniformly_certified(self):self.assertTrue(all(not a['mesh_uniform_compact_source_high_Sobolev_budget_proved'] for a in self.data['cases']))
 def test_pointwise_Weyl_open(self):self.assertTrue(self.data['original_both_Weyl_receiver_convergence_open'])
 def test_k0_identity(self):
  x=setup();self.assertTrue(np.array_equal(radial_A_power(x['P'],0,x['dr']),x['P']))
 def test_reject_negative_power(self):
  with self.assertRaises(ValueError):radial_A_power(setup()['U'],-1,.03)
 def test_nontrivial_compact_source_power(self):
  G=np.random.default_rng(4).normal(size=(3,7))
  self.assertGreater(np.linalg.norm(source_A_power(G,1,.03)-G),.1)
if __name__=='__main__':unittest.main(verbosity=2)
