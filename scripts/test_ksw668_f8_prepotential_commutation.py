import unittest
from ksw668_f8_prepotential_commutation import fourier_symbol,commute_operator,report

class TTPrepotential(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.r=report()
 def test_generic_divergence_zero(self):self.assertTrue(self.r['symbol']['general_3d_fourier_transversality_exact'])
 def test_generic_trace_zero(self):self.assertTrue(self.r['symbol']['general_3d_tracefree_exact'])
 def test_polynomial_not_division_by_k(self):self.assertTrue(self.r['symbol']['no_singular_k_inverse'])
 def test_exact_chord_polarization(self):self.assertEqual(self.r['symbol']['k_along_x_TT_yy_symbol'],'kx^4')
 def test_bulk_commutation(self):self.assertTrue(self.r['operators']['original_5d_L_commutes_with_spatial_TT'])
 def test_boundary_commutation(self):self.assertTrue(self.r['operators']['original_moving_oblique_boundary_B_commutes_with_spatial_TT'])
 def test_no_false_physics(self):self.assertFalse(self.r['operators']['full_3D_receiver_and_both_Weyl_nonzero_proved'])

if __name__=='__main__':unittest.main(verbosity=2)
