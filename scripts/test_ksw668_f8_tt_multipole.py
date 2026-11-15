"""Exact compact TT l=0,2,4 and original moving PDE negative controls."""
import unittest
import mpmath as mp
import numpy as np
from ksw668_f8_tt_multipole import profiles,normalized_sources,propagate

PARAM=dict(dr=.012,dy=.016,dt=.0025,eps=.04,final_t=12.,
           pulse=.065,inside_chord=.012,r_outer=4.3,y_outer=3.0)
class OriginalTTMultipole(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.sol=propagate(**PARAM)
 def test_angular_modes(self):self.assertEqual([p[0] for p in profiles()],[0,2,4])
 def test_effective_dimensions(self):self.assertEqual(self.sol['effective_radial_dimensions'],[3,7,11])
 def test_source_origin(self):self.assertTrue(np.allclose([p[2] for p in profiles()],[-24,-32,16/35]))
 def test_source_compact(self):
  eps=.04;r=np.array([0,.002,.02,.03,.04,.08,1.])
  src=normalized_sources(eps,r)
  self.assertTrue(np.all(src[:,r>=eps]==0))
 def test_real_space_tt_identity(self):
  mp.mp.dps=50;eps=mp.mpf('.04')
  for uu in (.15,.35,.60,.85):
   r=eps*mp.mpf(str(uu))
   f=lambda q:mp.exp(1-1/(1-(q/eps)**2))
   actual=eps**4*(mp.diff(f,r,4)+2*mp.diff(f,r,3)/r-3*mp.diff(f,r,2)/r**2+3*mp.diff(f,r)/r**3)
   coeff=normalized_sources(float(eps),np.array([0.,float(r)]))[:,1]
   recovered=sum(uu**(2*j)*coeff[j] for j in range(3))
   self.assertAlmostEqual(float(actual),recovered,delta=max(1e-8,abs(float(actual))*1e-10))
 def test_photon_dark_source(self):self.assertGreater(self.sol['source_adjusted_brane_photon_margin'],0)
 def test_no_derivatives_after_evolution(self):self.assertTrue(self.sol['no_post_evolution_spatial_derivatives'])
 def test_no_fourier_inverse(self):self.assertTrue(self.sol['no_spatial_Fourier_Bessel_inverse'])
 def test_beyond_cone_leak_negative(self):
  self.assertGreater(abs(self.sol['far_TT_yy_scaled_by_eps4']),1e-8)
  self.assertFalse(self.sol['numerical_convergence_certified'])
 def test_exact_mode_sum(self):self.assertAlmostEqual(sum(self.sol['raw_mode_values']),self.sol['retarded_TT_yy_scaled_by_eps4'])
 def test_physical_not_claimed(self):
  self.assertFalse(self.sol['full_Weyl_receiver_certified'])
  self.assertFalse(self.sol['physical_graviton_measured'])
 def test_zero_source(self):
  no=propagate(**dict(PARAM,drive=0.))
  self.assertEqual(no['retarded_TT_yy_scaled_by_eps4'],0.)
  self.assertEqual(no['far_TT_yy_scaled_by_eps4'],0.)
 def test_invalid_cone(self):
  with self.assertRaises(ValueError):propagate(**dict(PARAM,eps=.07))
if __name__=='__main__':unittest.main(verbosity=2)
