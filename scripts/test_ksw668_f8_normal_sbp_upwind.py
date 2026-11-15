#!/usr/bin/env python3
import unittest
import numpy as np
from ksw668_f8_normal_sbp_upwind import (
 audit,legacy_counterexample,evaluate,derivative_plus,derivative_minus)
class NormalSBP(unittest.TestCase):
 def test_legacy_exact_integer_counterexample(self):self.assertEqual(legacy_counterexample()['exact_legacy_outgoing_energy'],'277/2')
 def test_legacy_positive_energy(self):self.assertGreater(legacy_counterexample()['old_homogeneous_energy_production'],0)
 def test_new_negative_energy(self):self.assertLess(legacy_counterexample()['new_SBP_homogeneous_energy_production'],0)
 def test_random_original_wall(self):self.assertEqual(audit()['SBP_samples'],9)
 def test_forced_wall_bound(self):
  p=np.array([1.,2.,-1.,0.]);m=np.array([0.,-1.,1.,2.])
  d=evaluate(2,p,m,2,.2)
  self.assertLessEqual(.4*d['energy_production_Q'],d['original_source_uniform_wall_bound'])
 def test_zero(self):self.assertEqual(evaluate(1.5,np.zeros(9),np.zeros(9))['energy_production_Q'],0)
 def test_forward_telescope(self):
  p=np.array([0.,0.,1.,1.,0.])
  self.assertAlmostEqual(sum(p*derivative_plus(p)), -.5*sum(np.diff(p)**2))
 def test_backward_telescope(self):
  m=np.linspace(0,1,8)
  self.assertAlmostEqual(sum(m*derivative_minus(m)),.5*(m[-1]**2-m[0]**2+sum(np.diff(m)**2)))
 def test_nonzero_inhom(self):
  p=np.arange(8.,dtype=float);p[-1]=0
  self.assertTrue(evaluate(4/3,p,np.ones(8),1)['exact_SBP_holds'])
 def test_reject_bad_remote(self):
  with self.assertRaises(ValueError):evaluate(1.5,np.ones(8),np.zeros(8))
 def test_no_full_promotion(self):self.assertFalse(audit()['original_moving_full_discrete_SSPRK3_energy_closed'])
 def test_receiver_open(self):self.assertFalse(audit()['actual_early_Weyl_receiver_converged'])
if __name__=='__main__':unittest.main(verbosity=2)
