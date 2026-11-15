#!/usr/bin/env python3
import unittest,math
import numpy as np
from ksw668_f8_normal_sbp2_sat import derivative,sbp_identity,physical_rhs,audit
class OriginalSBP2SAT(unittest.TestCase):
 def test_nine_original_samples(self):self.assertEqual(audit()['verified_original_neumann_samples'],9)
 def test_constant_derivative(self):self.assertTrue(np.allclose(derivative(np.ones(16)),0))
 def test_linear_all_nodes(self):
  h=.1;y=np.arange(16)*h
  self.assertTrue(np.allclose(derivative(y,h),1))
 def test_quadratic_interior(self):
  h=.1;y=np.arange(16)*h
  self.assertTrue(np.allclose(derivative(y*y,h)[1:-1],2*y[1:-1]))
 def test_sbp_random(self):
  for n in (3,5,32):
   u=np.random.default_rng(n).normal(size=n)
   a,b=sbp_identity(u,.007);self.assertAlmostEqual(a,b,places=10)
 def test_zero_energy(self):
  z=np.zeros(15)
  _,_,d=physical_rhs(z,z,1.5,0);self.assertEqual(d['energy_derivative'],0)
 def test_forced_flux(self):
  p=np.arange(20.,dtype=float);m=-p
  _,_,d=physical_rhs(p,m,4/3,2)
  self.assertLessEqual(d['energy_derivative'],2*math.sqrt(5)*4+1e-8)
 def test_weak_not_strong(self):
  a=np.ones(12)
  _,_,d=physical_rhs(a,a,1,0)
  self.assertFalse(d['pointwise_strong_neumann_enforced'])
  self.assertNotEqual(d['weak_boundary_residual'],0)
 def test_original_source(self):self.assertTrue(audit()['exact_normal_semidiscrete_source_energy_bound_closed'])
 def test_no_RK3_promotion(self):self.assertFalse(audit()['original_full_time_discrete_coupled_energy_proved'])
 def test_Weyl_open(self):self.assertFalse(audit()['early_Weyl_receiver_converged'])
 def test_reject_time(self):
  with self.assertRaises(ValueError):physical_rhs(np.ones(8),np.ones(8),3,0)
 def test_reject_small_grid(self):
  with self.assertRaises(ValueError):sbp_identity(np.ones(2))
if __name__=='__main__':unittest.main(verbosity=2)
