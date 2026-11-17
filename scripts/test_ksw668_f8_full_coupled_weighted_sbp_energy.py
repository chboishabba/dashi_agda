#!/usr/bin/env python3
import unittest,math
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import (
 coeff,radial_stiffness,sbp_D,weighted_normal_D,setup,
 full_energy_derivative,algebra,audit)

class OriginalFullCoupledWeightedEnergy(unittest.TestCase):
 def test_t43_original_wall(self):
  b,v,vt,a,c=coeff(4/3)
  self.assertAlmostEqual(v,-.6);self.assertAlmostEqual(b,.75)
  self.assertAlmostEqual(a,.2);self.assertAlmostEqual(c,.8)
 def test_warp_weight_cancel(self):self.assertIn('P*M',algebra()['original_bulk_warp_weight_cancellation'])
 def test_forced_wall_not_G2(self):self.assertFalse(algebra()['positive_source_only_wall_bound_from_full_symmetrizer'])
 def test_uniform_bound_five(self):
  for t in np.linspace(1,12,151):
   b,v,vt,a,c=coeff(float(t));alpha=3*abs(v)/(2*b)
   self.assertAlmostEqual(alpha/(2*math.sqrt(a*c)),1.5,places=12)
   self.assertLessEqual(vt/(4*a),1)
   self.assertLessEqual(alpha,1.5)
 def test_weighted_SBP_exact(self):
  rng=np.random.default_rng(4)
  for n in (4,8,32):
   dy=.03;z=1/1.6+np.arange(n)*dy;w=z**(-3)
   H=np.full(n,dy);H[0]=H[-1]=dy/2
   p=rng.normal(size=n)
   lhs=np.dot(H*w*p,weighted_normal_D(p,z,dy))
   rhs=.5*(w[-1]*p[-1]**2-w[0]*p[0]**2)+np.dot(H*w,1.5*p*p/z)
   self.assertAlmostEqual(lhs,rhs,places=10)
 def test_weighted_interior_second_order(self):
  err=[]
  for h in (.05,.025,.0125):
   z=.5+np.arange(int(.4/h)+1)*h
   i=int(.2/h);err.append(abs(weighted_normal_D(np.ones(len(z)),z,h)[i]))
  self.assertLess(err[1]/err[0],.30);self.assertLess(err[2]/err[1],.30)
 def test_radial_FV_symmetric_negative(self):
  for d in (3,7,11):
   L,V=radial_stiffness(d,9,.03)
   self.assertLess(max(np.linalg.eigvals(L).real),0)
   self.assertTrue(np.allclose(V[:,None]*L,L.T*V[None,:]))
 def test_full_energy_t1(self):
  r=full_energy_derivative(setup(t=1.))
  self.assertLess(abs(r['exact_identity_residual']),1e-10)
  self.assertTrue(r['homogeneous_semidiscrete_Eprime_below_5E'])
 def test_full_energy_t43(self):
  r=full_energy_derivative(setup(t=4/3,ny=13,nr=7,seed=22))
  self.assertLess(abs(r['exact_identity_residual']),1e-10)
  self.assertTrue(r['homogeneous_semidiscrete_Eprime_below_5E'])
 def test_full_energy_t2(self):
  r=full_energy_derivative(setup(t=2,ny=17,nr=9,seed=33))
  self.assertLess(abs(r['exact_identity_residual']),1e-10)
  self.assertTrue(r['homogeneous_semidiscrete_Eprime_below_5E'])
 def test_forced_identity_not_promotion(self):
  d=setup();G=np.zeros((3,7));G[:,0]=.3
  r=full_energy_derivative(d,G)
  self.assertLess(abs(r['exact_identity_residual']),1e-10)
  self.assertFalse(r['original_physical_nonzero_source_homogeneous_energy_closed'])
 def test_arbitrary_original_grids(self):
  for i in range(4):
   d=setup(ny=6+i,nr=4+i,dy=.014+i*.003,dr=.02+i*.006,t=1+i/3,seed=i)
   self.assertLess(abs(full_energy_derivative(d)['exact_identity_residual']),1e-10)
 def test_no_pure_wall_source_quadratic_bound(self):
  _,v,_,_,_=coeff(1.5);beta=(1+v)/(1-v)
  for N in (1,10,100):
   p=-N/(1+v);m=beta*p;G=1.
   wall=-((1+v)*p-(1-v)*m)**2/4-(1-v)*m*G
   self.assertAlmostEqual(wall,N)
 def test_no_RK3_or_both_Weyl_promotion(self):
  x=audit()
  self.assertFalse(x['original_full_SSPRK3_closed'])
  self.assertFalse(x['both_Weyl_receiver_converged'])
 def test_long_baseline_original_t12(self):
  r=full_energy_derivative(setup(t=12.,ny=15,nr=7,seed=43))
  self.assertLess(abs(r['exact_identity_residual']),1e-10)
  self.assertTrue(r['homogeneous_semidiscrete_Eprime_below_5E'])
 def test_invalid_time(self):
  with self.assertRaises(ValueError):coeff(.5)

if __name__=='__main__':unittest.main(verbosity=2)
