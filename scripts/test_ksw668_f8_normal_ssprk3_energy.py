#!/usr/bin/env python3
import unittest,math
import numpy as np
from ksw668_f8_normal_ssprk3_energy import (
 NORMAL_CFL_RATIO,energy,forward_euler,ssprk3,audit)
class OriginalNormalSSPRK3(unittest.TestCase):
 def test_exact_CFL(self):self.assertAlmostEqual(NORMAL_CFL_RATIO,2-math.sqrt(2))
 def test_stage_weights(self):self.assertEqual(audit()['forced_SSPRK3_stage_weights'],['1/6','2/3','1/6'])
 def test_nine_scenarios(self):self.assertEqual(audit()['validated_scenarios'],9)
 def test_vector_forced_bound(self):
  P=np.ones((2,32));M=-P.copy()
  _,_,d=ssprk3(P,M,1,1.5,2,np.array([1.,2.]),np.array([3.,4.]),np.array([5.,6.]),.45)
  self.assertLessEqual(d['ssprk3_normal_energy_gain'],d['forced_SSPRK3_energy_upper_bound'])
 def test_zero_source_nonexpansive(self):
  P=np.ones((3,16));M=np.ones_like(P)
  _,_,d=ssprk3(P,M,1,1.5,2,np.zeros(3),np.zeros(3),np.zeros(3),.45)
  self.assertLessEqual(d['ssprk3_normal_energy_gain'],1e-10)
 def test_zero_state(self):
  P=np.zeros((1,8));M=P.copy()
  p,m,_=ssprk3(P,M,1,1.5,2,np.zeros(1),np.zeros(1),np.zeros(1),.45)
  self.assertEqual(energy(p,m),0)
 def test_FE_moving_source(self):
  P=np.arange(8.,dtype=float)[None,:];M=-P
  _,_,d=forward_euler(P,M,4/3,np.array([2.]),.5)
  self.assertLessEqual(d['delta_energy'],.5*d['wall_flux']+1e-9)
 def test_zero_step(self):
  P=np.ones((1,8));M=P.copy()
  p,m,_=forward_euler(P,M,1,np.array([20.]),0)
  self.assertEqual(energy(p,m),energy(P,M))
 def test_reject_overCFL(self):
  P=np.ones((1,8));M=P.copy()
  with self.assertRaises(ValueError):forward_euler(P,M,1,np.array([0.]),.6)
 def test_actual_overCFL_growth_witness(self):
  gamma=.8*(1+1/math.sqrt(2))
  M=np.array([(-1)**i for i in range(32)],float)
  nextM=(1-gamma)*M+gamma*np.r_[0,M[:-1]]
  self.assertGreater(np.dot(nextM,nextM),np.dot(M,M))
 def test_3channels(self):
  rng=np.random.default_rng(42);P=rng.normal(size=(3,14));M=rng.normal(size=(3,14))
  p,m,_=ssprk3(P,M,1,1.4,2,np.zeros(3),np.zeros(3),np.zeros(3),.4)
  self.assertLess(energy(p,m),energy(P,M))
 def test_no_full_promotion(self):self.assertTrue(audit()['original_full_radial_warp_coupled_CFL_still_open'])
 def test_no_Weyl_promotion(self):self.assertTrue(audit()['original_receiver_Weyl_convergence_still_open'])
if __name__=='__main__':unittest.main(verbosity=2)
