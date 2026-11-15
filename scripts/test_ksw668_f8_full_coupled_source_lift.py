#!/usr/bin/env python3
import unittest
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import setup,coeff
from ksw668_f8_full_coupled_source_lift import chi_compact,source_lift,check,audit
class OriginalFullCoupledForcedSource(unittest.TestCase):
 def test_compact_cutoff(self):
  c=chi_compact(np.linspace(0,.15,16),.05)
  self.assertEqual(c[0],1.);self.assertTrue(np.all(c[5:]==0))
 def test_exact_wall_Israel_target(self):
  d=setup(t=4/3,seed=13);G=np.ones((3,7));GT=np.ones_like(G)
  l=source_lift(d,G,GT,cutoff=.15);_,v,_,_,_=coeff(4/3)
  self.assertTrue(np.allclose(l['lift_M'][:,0,:],-2*G/(1-v)))
 def test_poincare_time_derivative_lift(self):
  d=setup(t=1.5,seed=15);G=np.random.default_rng(3).normal(size=(3,7))
  GT=np.zeros_like(G);l=source_lift(d,G,GT)
  eps=1e-5;t=1.5;delta=eps*t*t/np.sqrt(1+t*t)
  plus={**d,'t':t+delta};minus={**d,'t':t-delta}
  approx=(source_lift(plus,G,GT)['lift_M']-source_lift(minus,G,GT)['lift_M'])/(2*eps)
  self.assertLess(np.max(abs(approx-l['lift_M_T'])),4e-7)
 def test_original_full_forced_t1(self):
  d=setup(t=1,seed=13);G=np.ones((3,7))*.02
  self.assertLess(check(d,G,G*.5)['exact_lift_residual'],1e-9)
 def test_original_full_forced_t43(self):
  d=setup(t=4/3,seed=13);G=np.ones((3,7))*.02;r=check(d,G,G*.5)
  self.assertLess(r['Eprime_with_volume_force'],r['Eprime_upper_6E_half_Fnorm'])
 def test_original_full_forced_t2(self):
  d=setup(t=2,seed=15);G=np.ones((3,7))*.02
  self.assertLess(check(d,G,G*.5)['exact_lift_residual'],1e-9)
 def test_nontrivial_original_radial_source(self):
  d=setup(t=1.7,seed=9);rng=np.random.default_rng(42)
  G=rng.normal(size=(3,7))*.01;GT=rng.normal(size=(3,7))*.01
  self.assertTrue(check(d,G,GT,cutoff=.06)['original_coupled_forced_semidiscrete_energy_closed'])
 def test_zero_source(self):
  d=setup();G=np.zeros((3,7))
  self.assertEqual(check(d,G,G)['source_weighted_norm_sq'],0)
 def test_missing_time_derivative_detected(self):
  d=setup();G=np.zeros((3,7));GT=np.ones((3,7))*.01
  self.assertGreater(np.linalg.norm(source_lift(d,G,GT)['F_M']),0)
 def test_bad_source_shape(self):
  with self.assertRaises(ValueError):source_lift(setup(),np.ones((2,7)),np.zeros((2,7)))
 def test_no_full_or_both_Weyl_promotion(self):
  x=audit()
  self.assertTrue(x['entire_coupled_RK3_and_Weyl_receiver_convergence_open'])
if __name__=='__main__':unittest.main(verbosity=2)
