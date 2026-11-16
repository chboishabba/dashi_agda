import unittest
from ksw668_f8_threegrid_signed_failclosed import verify
class OriginalTTWeylRadialNormalFactorial(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.a=verify()['fixed_dt_radial_normal_factorial']
 def test_identical_dt(self):self.assertAlmostEqual(self.a['common_dt'],.0011998047821762945)
 def test_four_arms(self):self.assertEqual(set(self.a['grid_arms']),{'A','B','C','D'})
 def test_all_modal_E4(self):self.assertEqual(len(self.a['signed_modewise']['E4']),3)
 def test_all_modal_E5(self):self.assertEqual(len(self.a['signed_modewise']['E5']),3)
 def test_radial_dominates_ell0_E4(self):self.assertGreater(abs(self.a['signed_modewise']['E4'][0]['radial_fraction_of_signed_total']),.95)
 def test_radial_dominates_ell2_E4(self):self.assertGreater(abs(self.a['signed_modewise']['E4'][1]['radial_fraction_of_signed_total']),.95)
 def test_ell0_radial_over_normal_E4(self):
  x=self.a['signed_modewise']['E4'][0];self.assertGreater(abs(x['radial_change']),100*abs(x['normal_change']))
 def test_exact_telescoping(self):
  for rs in self.a['signed_modewise'].values():
   for x in rs:self.assertAlmostEqual(x['radial_change']+x['normal_change']+x['interaction'],x['total_change'],places=11)
 def test_wavefront_and_source_not_separated(self):self.assertTrue(self.a['source_vs_FV_wavefront_error_not_yet_separated'])
 def test_no_continuum_bound_from_factorial(self):self.assertFalse(self.a['is_proven_continuum_error_bound'])
if __name__=='__main__':unittest.main()
